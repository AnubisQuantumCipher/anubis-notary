#!/usr/bin/env node
/**
 * Mina Bridge - Node.js subprocess bridge for Anubis Notary
 *
 * This script bridges the Rust anubis_io crate with the Mina Protocol
 * blockchain via the o1js library. It communicates over stdin/stdout
 * using JSON messages.
 *
 * ## Protocol
 *
 * Request format:
 * ```json
 * {"cmd": "anchor|verify|time|balance|shutdown", ...params}
 * ```
 *
 * Response format:
 * ```json
 * {"ok": true, ...result} or {"ok": false, "error": "message"}
 * ```
 *
 * ## Environment Variables
 *
 * - MINA_NETWORK: "mainnet", "devnet", or "local"
 * - MINA_GRAPHQL_URL: GraphQL endpoint URL
 * - MINA_ZKAPP_ADDRESS: zkApp contract address
 * - MINA_PRIVATE_KEY: Wallet private key for signing
 * - MINA_FEE: Transaction fee in nanomina
 */

import { Mina, PrivateKey, PublicKey, Field, fetchAccount, AccountUpdate } from 'o1js';
import { AnubisAnchor, hexToField } from './build/index.js';
import * as readline from 'readline';

// Network configuration
const NETWORKS = {
  mainnet: {
    graphqlUrl: 'https://api.minascan.io/node/mainnet/v1/graphql',
    archiveUrl: 'https://api.minascan.io/archive/mainnet/v1/graphql',
    explorerUrl: 'https://minascan.io/mainnet',
    accountCreationFee: 1_000_000_000n, // 1 MINA
  },
  devnet: {
    graphqlUrl: 'https://api.minascan.io/node/devnet/v1/graphql',
    archiveUrl: 'https://api.minascan.io/archive/devnet/v1/graphql',
    explorerUrl: 'https://minascan.io/devnet',
    accountCreationFee: 1_000_000_000n, // 1 MINA
  },
  local: {
    graphqlUrl: 'http://localhost:8080/graphql',
    archiveUrl: 'http://localhost:8081/graphql',
    explorerUrl: 'http://localhost:8080',
    accountCreationFee: 1_000_000_000n,
  },
};

// Official AnubisAnchor zkApp on Mina mainnet (public use)
const OFFICIAL_ZKAPP_ADDRESS = 'B62qmddzKWzKQmNYsxxJRU6kTHtKxBaCwECEGUtdsz1DCTTK57XFceW';

// Configuration from environment (defaults to mainnet with official zkApp)
const networkName = process.env.MINA_NETWORK || 'mainnet';
const networkConfig = NETWORKS[networkName] || NETWORKS.mainnet;

const config = {
  network: networkName,
  graphqlUrl: process.env.MINA_GRAPHQL_URL || networkConfig.graphqlUrl,
  archiveUrl: networkConfig.archiveUrl,
  explorerUrl: networkConfig.explorerUrl,
  // Default to official zkApp on mainnet - users just need MINA_PRIVATE_KEY
  zkappAddress: process.env.MINA_ZKAPP_ADDRESS || OFFICIAL_ZKAPP_ADDRESS,
  privateKey: process.env.MINA_PRIVATE_KEY || '',
  fee: BigInt(process.env.MINA_FEE || '100000000'),
  accountCreationFee: networkConfig.accountCreationFee,
};

// Global state
let zkApp = null;
let zkAppAddress = null;
let senderKey = null;
let senderAddress = null;
let isInitialized = false;
let isCompiled = false;
let verificationKey = null;

/**
 * Debug logging (to stderr to not interfere with protocol).
 */
function logDebug(message) {
  if (process.env.MINA_DEBUG === '1') {
    console.error(`[mina-bridge] ${message}`);
  }
}

/**
 * Initialize the Mina network connection and zkApp.
 */
async function initialize() {
  if (isInitialized) return;

  try {
    logDebug('Configuring Mina network...');
    const Network = Mina.Network({
      mina: config.graphqlUrl,
      networkId: config.network === 'mainnet' ? 'mainnet' : 'testnet',
    });
    Mina.setActiveInstance(Network);

    if (config.zkappAddress) {
      zkAppAddress = PublicKey.fromBase58(config.zkappAddress);
      zkApp = new AnubisAnchor(zkAppAddress);
      logDebug(`zkApp address: ${config.zkappAddress}`);
    }

    if (config.privateKey) {
      senderKey = PrivateKey.fromBase58(config.privateKey);
      senderAddress = senderKey.toPublicKey();
      logDebug(`Sender address: ${senderAddress.toBase58()}`);
    }

    isInitialized = true;
    logDebug('Mina connection initialized');
  } catch (error) {
    throw new Error(`Failed to initialize: ${error.message}`);
  }
}

/**
 * Compile the zkApp contract (required before creating proofs).
 */
async function compileContract() {
  if (isCompiled) return;

  try {
    logDebug('Compiling AnubisAnchor contract...');
    const result = await AnubisAnchor.compile();
    verificationKey = result.verificationKey;
    isCompiled = true;
    logDebug('Contract compiled successfully');
  } catch (error) {
    throw new Error(`Failed to compile contract: ${error.message}`);
  }
}

/**
 * Anchor a Merkle root to the blockchain.
 */
async function handleAnchor(request) {
  await initialize();
  await compileContract();

  if (!zkApp || !zkAppAddress) {
    throw new Error('zkApp not configured - set MINA_ZKAPP_ADDRESS');
  }
  if (!senderKey || !senderAddress) {
    throw new Error('Wallet not configured - set MINA_PRIVATE_KEY');
  }

  const rootHex = request.root;
  if (!rootHex || rootHex.length !== 64) {
    throw new Error('Invalid root: must be 64 hex characters (32 bytes)');
  }

  const rootField = hexToField(rootHex);

  logDebug('Fetching account state...');
  await fetchAccount({ publicKey: zkAppAddress });
  await fetchAccount({ publicKey: senderAddress });

  logDebug('Creating anchor transaction...');
  const tx = await Mina.transaction(
    { sender: senderAddress, fee: config.fee },
    async () => {
      await zkApp.anchorRoot(rootField);
    }
  );

  logDebug('Proving transaction...');
  await tx.prove();

  logDebug('Signing and sending transaction...');
  tx.sign([senderKey]);
  const pendingTx = await tx.send();

  if (!pendingTx.status === 'pending') {
    throw new Error('Transaction failed to send');
  }

  const txHash = pendingTx.hash;
  logDebug(`Transaction sent: ${txHash}`);

  // Wait for inclusion if requested
  if (request.wait) {
    logDebug('Waiting for transaction inclusion...');
    try {
      await pendingTx.wait();
      logDebug('Transaction included');
    } catch (e) {
      logDebug(`Wait failed (may still be pending): ${e.message}`);
    }
  }

  return {
    ok: true,
    address: zkAppAddress.toBase58(),
    tx: txHash,
    timestamp: Date.now(),
  };
}

/**
 * Verify a Merkle root exists on-chain.
 */
async function handleVerify(request) {
  await initialize();

  if (!zkApp || !zkAppAddress) {
    throw new Error('zkApp not configured - set MINA_ZKAPP_ADDRESS');
  }

  const rootHex = request.root;
  if (!rootHex || rootHex.length !== 64) {
    throw new Error('Invalid root: must be 64 hex characters (32 bytes)');
  }

  await fetchAccount({ publicKey: zkAppAddress });

  const onChainRoot = zkApp.merkleRoot.get();
  const providedRoot = hexToField(rootHex);
  const isMatch = onChainRoot.equals(providedRoot).toBoolean();

  return {
    ok: true,
    verified: isMatch,
    currentRoot: onChainRoot.toString(),
  };
}

/**
 * Get current blockchain time.
 */
async function handleTime() {
  await initialize();

  try {
    const response = await fetch(config.graphqlUrl, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        query: `
          query {
            bestChain(maxLength: 1) {
              protocolState {
                consensusState {
                  blockHeight
                }
                blockchainState {
                  utcDate
                }
              }
            }
          }
        `,
      }),
    });

    const data = await response.json();
    const block = data?.data?.bestChain?.[0];

    if (!block) {
      throw new Error('No block data available');
    }

    const height = Number(block.protocolState.consensusState.blockHeight);
    const timestamp = Number(block.protocolState.blockchainState.utcDate);

    return {
      ok: true,
      height: height,
      timestamp: timestamp,
    };
  } catch (error) {
    throw new Error(`Failed to get time: ${error.message}`);
  }
}

/**
 * Get wallet balance.
 */
async function handleBalance() {
  await initialize();

  if (!senderAddress) {
    throw new Error('Wallet not configured - set MINA_PRIVATE_KEY');
  }

  try {
    await fetchAccount({ publicKey: senderAddress });
    const balance = Mina.getBalance(senderAddress);
    const balanceNanomina = balance.toBigInt();

    return {
      ok: true,
      address: senderAddress.toBase58(),
      balance: Number(balanceNanomina),
      balanceMina: Number(balanceNanomina) / 1e9,
    };
  } catch (error) {
    throw new Error(`Failed to get balance: ${error.message}`);
  }
}

/**
 * Generate a new Mina keypair.
 */
async function handleKeygen() {
  const privateKey = PrivateKey.random();
  const publicKey = privateKey.toPublicKey();

  return {
    ok: true,
    privateKey: privateKey.toBase58(),
    publicKey: publicKey.toBase58(),
    network: config.network,
    message: 'SAVE THE PRIVATE KEY SECURELY - IT CANNOT BE RECOVERED',
  };
}

/**
 * Deploy the AnubisAnchor zkApp contract.
 */
async function handleDeploy(request) {
  await initialize();
  await compileContract();

  if (!senderKey || !senderAddress) {
    throw new Error('Wallet not configured - set MINA_PRIVATE_KEY');
  }

  if (!verificationKey) {
    throw new Error('Contract not compiled - verificationKey missing');
  }

  // Generate zkApp keypair if not provided
  let zkAppPrivateKey;
  let zkAppPublicKey;

  if (request.zkappPrivateKey) {
    zkAppPrivateKey = PrivateKey.fromBase58(request.zkappPrivateKey);
    zkAppPublicKey = zkAppPrivateKey.toPublicKey();
  } else {
    zkAppPrivateKey = PrivateKey.random();
    zkAppPublicKey = zkAppPrivateKey.toPublicKey();
  }

  logDebug(`Deploying zkApp to address: ${zkAppPublicKey.toBase58()}`);
  logDebug(`Fee payer: ${senderAddress.toBase58()}`);

  // Fetch fee payer account
  await fetchAccount({ publicKey: senderAddress });

  // Create the zkApp instance
  const zkAppInstance = new AnubisAnchor(zkAppPublicKey);

  // Calculate deployment fee (includes account creation)
  const deployFee = config.fee + config.accountCreationFee;

  logDebug(`Deployment fee: ${Number(deployFee) / 1e9} MINA`);

  // Create deployment transaction with proper account funding
  const tx = await Mina.transaction(
    { sender: senderAddress, fee: deployFee },
    async () => {
      AccountUpdate.fundNewAccount(senderAddress);
      await zkAppInstance.deploy({ verificationKey });
    }
  );

  logDebug('Proving deployment transaction...');
  await tx.prove();

  logDebug('Signing deployment transaction...');
  tx.sign([senderKey, zkAppPrivateKey]);

  logDebug('Sending deployment transaction...');
  const pendingTx = await tx.send();

  if (pendingTx.status !== 'pending') {
    throw new Error('Deployment transaction failed to send');
  }

  const txHash = pendingTx.hash;
  logDebug(`Deployment transaction sent: ${txHash}`);

  // Wait for confirmation if requested
  if (request.wait) {
    logDebug('Waiting for deployment confirmation...');
    try {
      await pendingTx.wait();
      logDebug('Deployment confirmed');
    } catch (e) {
      logDebug(`Wait error (may still be pending): ${e.message}`);
    }
  }

  return {
    ok: true,
    zkappAddress: zkAppPublicKey.toBase58(),
    zkappPrivateKey: zkAppPrivateKey.toBase58(),
    deployerAddress: senderAddress.toBase58(),
    txHash: txHash,
    network: config.network,
    explorerUrl: `${config.explorerUrl}/tx/${txHash}`,
    message: 'SAVE THE ZKAPP PRIVATE KEY - needed only for contract upgrades',
  };
}

/**
 * Get network info.
 */
async function handleNetworkInfo() {
  return {
    ok: true,
    network: config.network,
    graphqlUrl: config.graphqlUrl,
    explorerUrl: config.explorerUrl,
    accountCreationFee: Number(config.accountCreationFee) / 1e9,
    transactionFee: Number(config.fee) / 1e9,
    totalDeploymentCost: Number(config.fee + config.accountCreationFee) / 1e9,
  };
}

/**
 * Process a single command.
 */
async function processCommand(line) {
  try {
    const request = JSON.parse(line.trim());
    const cmd = request.cmd;

    let result;
    switch (cmd) {
      case 'anchor':
        result = await handleAnchor(request);
        break;
      case 'verify':
        result = await handleVerify(request);
        break;
      case 'time':
        result = await handleTime();
        break;
      case 'balance':
        result = await handleBalance();
        break;
      case 'keygen':
        result = await handleKeygen();
        break;
      case 'deploy':
        result = await handleDeploy(request);
        break;
      case 'networkinfo':
        result = await handleNetworkInfo();
        break;
      case 'shutdown':
        console.log(JSON.stringify({ ok: true, message: 'shutting down' }));
        process.exit(0);
        break;
      default:
        throw new Error(`Unknown command: ${cmd}`);
    }

    console.log(JSON.stringify(result));
  } catch (error) {
    console.log(JSON.stringify({
      ok: false,
      error: error.message || 'Unknown error',
    }));
  }
}

/**
 * Main entry point.
 */
async function main() {
  logDebug('Starting Mina bridge...');
  logDebug(`Network: ${config.network}`);
  logDebug(`GraphQL: ${config.graphqlUrl}`);
  logDebug(`zkApp: ${config.zkappAddress || '(not set)'}`);
  logDebug(`Wallet: ${config.privateKey ? '(configured)' : '(not set)'}`);

  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    terminal: false,
  });

  rl.on('line', async (line) => {
    if (line.trim()) {
      await processCommand(line);
    }
  });

  rl.on('close', () => {
    logDebug('stdin closed, exiting');
    process.exit(0);
  });

  process.on('uncaughtException', (error) => {
    console.error(`[mina-bridge] Uncaught exception: ${error.message}`);
    process.exit(1);
  });

  process.on('unhandledRejection', (reason) => {
    console.error(`[mina-bridge] Unhandled rejection: ${reason}`);
  });

  logDebug('Ready for commands');
}

main().catch((error) => {
  console.error(`[mina-bridge] Fatal error: ${error.message}`);
  process.exit(1);
});
