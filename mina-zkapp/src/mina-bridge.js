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
 *
 * ## Commands
 *
 * - anchor: Submit a Merkle root to the zkApp
 * - verify: Check if a root exists on-chain
 * - time: Get current blockchain time
 * - balance: Get wallet balance
 * - shutdown: Gracefully exit
 */

import { Mina, PrivateKey, PublicKey, Field, fetchAccount } from 'o1js';
import { AnubisAnchor, hexToField } from './index.js';
import * as readline from 'readline';

// Configuration from environment
const config = {
  network: process.env.MINA_NETWORK || 'devnet',
  graphqlUrl: process.env.MINA_GRAPHQL_URL || 'https://devnet.minaexplorer.com/graphql',
  zkappAddress: process.env.MINA_ZKAPP_ADDRESS || '',
  privateKey: process.env.MINA_PRIVATE_KEY || '',
  fee: BigInt(process.env.MINA_FEE || '100000000'), // 0.1 MINA default
};

// Global state
let zkApp = null;
let zkAppAddress = null;
let senderKey = null;
let senderAddress = null;
let isInitialized = false;

/**
 * Initialize the Mina network connection and zkApp.
 */
async function initialize() {
  if (isInitialized) return;

  try {
    // Configure network
    const Network = Mina.Network({
      mina: config.graphqlUrl,
      archive: config.graphqlUrl.replace('/graphql', '/archive'),
    });
    Mina.setActiveInstance(Network);

    // Parse zkApp address
    if (config.zkappAddress) {
      zkAppAddress = PublicKey.fromBase58(config.zkappAddress);
      zkApp = new AnubisAnchor(zkAppAddress);
    }

    // Parse sender key if provided
    if (config.privateKey) {
      senderKey = PrivateKey.fromBase58(config.privateKey);
      senderAddress = senderKey.toPublicKey();
    }

    isInitialized = true;
    logDebug('Initialized Mina connection');
  } catch (error) {
    throw new Error(`Failed to initialize: ${error.message}`);
  }
}

/**
 * Anchor a Merkle root to the blockchain.
 */
async function handleAnchor(request) {
  await initialize();

  if (!zkApp || !zkAppAddress) {
    throw new Error('zkApp not configured');
  }
  if (!senderKey || !senderAddress) {
    throw new Error('Wallet not configured');
  }

  const rootHex = request.root;
  if (!rootHex || rootHex.length !== 64) {
    throw new Error('Invalid root: must be 64 hex characters (32 bytes)');
  }

  // Convert hex to Field
  const rootField = hexToField(rootHex);

  // Fetch account state
  await fetchAccount({ publicKey: zkAppAddress });
  await fetchAccount({ publicKey: senderAddress });

  // Create and prove transaction
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

  if (!pendingTx.isSuccess) {
    throw new Error('Transaction failed to send');
  }

  // Wait for inclusion
  logDebug('Waiting for transaction inclusion...');
  const includedTx = await pendingTx.wait();

  // Get block info
  const blockHeight = includedTx.blockHeight || 0;
  const timestamp = Date.now(); // Approximate; real implementation would query block

  return {
    ok: true,
    address: zkAppAddress.toBase58(),
    tx: pendingTx.hash,
    height: Number(blockHeight),
    timestamp: timestamp,
    proof: null, // Proof generation would be added here
  };
}

/**
 * Verify a Merkle root exists on-chain.
 */
async function handleVerify(request) {
  await initialize();

  if (!zkApp || !zkAppAddress) {
    throw new Error('zkApp not configured');
  }

  const rootHex = request.root;
  if (!rootHex || rootHex.length !== 64) {
    throw new Error('Invalid root: must be 64 hex characters (32 bytes)');
  }

  // Fetch current state
  await fetchAccount({ publicKey: zkAppAddress });

  // Get on-chain root
  const onChainRoot = zkApp.merkleRoot.get();
  const providedRoot = hexToField(rootHex);

  // Check if matches current root
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
    // Query network status
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
    throw new Error('Wallet not configured');
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
 * Debug logging (to stderr to not interfere with protocol).
 */
function logDebug(message) {
  if (process.env.MINA_DEBUG === '1') {
    console.error(`[mina-bridge] ${message}`);
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

  // Create readline interface for stdin
  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    terminal: false,
  });

  // Process each line as a command
  rl.on('line', async (line) => {
    if (line.trim()) {
      await processCommand(line);
    }
  });

  // Handle close
  rl.on('close', () => {
    logDebug('stdin closed, exiting');
    process.exit(0);
  });

  // Handle errors
  process.on('uncaughtException', (error) => {
    console.error(`[mina-bridge] Uncaught exception: ${error.message}`);
    process.exit(1);
  });

  process.on('unhandledRejection', (reason) => {
    console.error(`[mina-bridge] Unhandled rejection: ${reason}`);
  });

  logDebug('Ready for commands');
}

// Run
main().catch((error) => {
  console.error(`[mina-bridge] Fatal error: ${error.message}`);
  process.exit(1);
});
