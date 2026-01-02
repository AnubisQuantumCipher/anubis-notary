#!/usr/bin/env node
/**
 * Starknet Bridge - Node.js subprocess bridge for Anubis Notary
 *
 * This script bridges the Rust anubis_io crate with Starknet
 * via the starknet.js library. It communicates over stdin/stdout
 * using JSON messages.
 *
 * ## Protocol
 *
 * Request format:
 * ```json
 * {"cmd": "anchor|verify|time|networkinfo|shutdown", ...params}
 * ```
 *
 * Response format:
 * ```json
 * {"ok": true, ...result} or {"ok": false, "error": "message"}
 * ```
 *
 * ## Environment Variables
 *
 * - STARKNET_NETWORK: "mainnet", "sepolia", or custom RPC URL
 * - STARKNET_CONTRACT: Contract address for NotaryOracle
 * - STARKNET_PRIVATE_KEY: Account private key
 * - STARKNET_ACCOUNT: Account address
 * - STARKNET_DEBUG: Set to "1" to enable debug logging
 */

import { Account, RpcProvider, Contract, hash } from 'starknet';
import * as readline from 'readline';

// Constants
const CONFIRMATION_POLL_INTERVAL_MS = 5000;  // 5 seconds between confirmation checks
const CAIRO_VERSION = "1";  // Cairo 1.0 for modern accounts (ArgentX, Braavos)

// Network configuration - using dRPC public endpoints (consistent with Rust code)
const NETWORKS = {
  mainnet: {
    rpcUrl: 'https://starknet-mainnet.drpc.org',
    explorerUrl: 'https://starkscan.co',
  },
  sepolia: {
    rpcUrl: 'https://starknet-sepolia.drpc.org',
    explorerUrl: 'https://sepolia.starkscan.co',
  },
};

// Official NotaryOracle contract on Sepolia
const OFFICIAL_CONTRACT_SEPOLIA = '0x04aa72f8dc65247389378621b6ff3e61852d56ddf571b522d03f02dc7f827606';

// NotaryOracle ABI - using Cairo 1.0 format
const NOTARY_ORACLE_ABI = [
  {
    "type": "interface",
    "name": "anubis_notary_oracle::INotaryOracle",
    "items": [
      {
        "type": "function",
        "name": "anchor_root",
        "inputs": [{"name": "root", "type": "core::felt252"}],
        "outputs": [{"type": "core::felt252"}],
        "state_mutability": "external"
      },
      {
        "type": "function",
        "name": "verify_root",
        "inputs": [{"name": "root", "type": "core::felt252"}],
        "outputs": [{"type": "core::bool"}],
        "state_mutability": "view"
      },
      {
        "type": "function",
        "name": "get_anchor_count",
        "inputs": [],
        "outputs": [{"type": "core::felt252"}],
        "state_mutability": "view"
      }
    ]
  },
  {
    "type": "impl",
    "name": "NotaryOracleImpl",
    "interface_name": "anubis_notary_oracle::INotaryOracle"
  }
];

// Configuration from environment
const networkName = process.env.STARKNET_NETWORK || 'sepolia';
const networkConfig = NETWORKS[networkName] || NETWORKS.sepolia;

const config = {
  network: networkName,
  rpcUrl: process.env.STARKNET_RPC || networkConfig.rpcUrl,
  explorerUrl: networkConfig.explorerUrl,
  contractAddress: process.env.STARKNET_CONTRACT || OFFICIAL_CONTRACT_SEPOLIA,
  privateKey: process.env.STARKNET_PRIVATE_KEY || '',
  accountAddress: process.env.STARKNET_ACCOUNT || '',
};

// Global state
let provider = null;
let account = null;
let contract = null;
let isInitialized = false;

/**
 * Debug logging (to stderr to not interfere with protocol).
 */
function logDebug(message) {
  if (process.env.STARKNET_DEBUG === '1') {
    console.error(`[starknet-bridge] ${message}`);
  }
}

/**
 * Convert a 32-byte hex hash to felt252 using Poseidon hash.
 */
function hashToFelt(hexHash) {
  const cleanHex = hexHash.startsWith('0x') ? hexHash.slice(2) : hexHash;

  if (cleanHex.length !== 64) {
    throw new Error(`Invalid hash length: expected 64 hex chars, got ${cleanHex.length}`);
  }

  // Validate hex characters
  if (!/^[0-9a-fA-F]{64}$/.test(cleanHex)) {
    throw new Error(`Invalid hex characters in hash: ${cleanHex}`);
  }

  // Split into two 128-bit chunks and Poseidon hash them
  const high = '0x' + cleanHex.slice(0, 32);
  const low = '0x' + cleanHex.slice(32, 64);

  return hash.computePoseidonHash(high, low);
}

/**
 * Initialize the Starknet connection.
 */
async function initialize() {
  if (isInitialized) return;

  try {
    logDebug('Configuring Starknet connection...');
    logDebug(`RPC: ${config.rpcUrl}`);

    provider = new RpcProvider({ nodeUrl: config.rpcUrl });

    if (config.privateKey && config.accountAddress) {
      // Create account - let starknet.js handle transaction version automatically
      account = new Account(
        provider,
        config.accountAddress,
        config.privateKey,
        CAIRO_VERSION
      );
      logDebug(`Account: ${config.accountAddress}`);
    }

    if (config.contractAddress && account) {
      contract = new Contract(NOTARY_ORACLE_ABI, config.contractAddress, account);
      logDebug(`Contract: ${config.contractAddress}`);
    }

    isInitialized = true;
    logDebug('Starknet connection initialized');
  } catch (error) {
    throw new Error(`Failed to initialize: ${error.message}`);
  }
}

/**
 * Anchor a receipt hash to the blockchain.
 */
async function handleAnchor(request) {
  await initialize();

  if (!account) {
    throw new Error('Account not configured - set STARKNET_PRIVATE_KEY and STARKNET_ACCOUNT');
  }
  if (!contract) {
    throw new Error('Contract not configured - set STARKNET_CONTRACT');
  }

  const rootHex = request.root;
  if (!rootHex || rootHex.length !== 64) {
    throw new Error('Invalid root: must be 64 hex characters (32 bytes)');
  }

  const rootFelt = hashToFelt(rootHex);
  logDebug(`Anchoring root: ${rootHex}`);
  logDebug(`As felt252: ${rootFelt}`);

  try {
    // Use account.execute with explicit calldata array
    // The anchor_root function takes a single felt252 argument
    const call = {
      contractAddress: config.contractAddress,
      entrypoint: 'anchor_root',
      calldata: [rootFelt],  // Direct array format
    };

    logDebug(`Call structure: ${JSON.stringify(call)}`);

    logDebug('Executing V3 transaction (auto-estimating fees)...');

    // Let starknet.js handle V3 fee estimation automatically
    const response = await account.execute(call);
    const txHash = response.transaction_hash;

    logDebug(`V3 Transaction submitted: ${txHash}`);

    let blockNumber = null;
    if (request.wait) {
      logDebug('Waiting for transaction confirmation...');
      const receipt = await provider.waitForTransaction(txHash, {
        retryInterval: CONFIRMATION_POLL_INTERVAL_MS,
      });
      blockNumber = receipt.block_number;
      logDebug(`Transaction confirmed in block ${blockNumber}`);
    }

    return {
      ok: true,
      tx: txHash,
      contract: config.contractAddress,
      network: config.network,
      explorerUrl: `${config.explorerUrl}/tx/${txHash}`,
      timestamp: Date.now(),
      block: blockNumber,
    };
  } catch (error) {
    logDebug(`Error type: ${error.constructor.name}`);
    logDebug(`Error message: ${error.message}`);
    if (error.cause) logDebug(`Error cause: ${error.cause}`);
    throw new Error(`Anchor failed: ${error.message}`);
  }
}

/**
 * Verify a root exists on-chain.
 */
async function handleVerify(request) {
  await initialize();

  if (!contract) {
    throw new Error('Contract not configured - set STARKNET_CONTRACT');
  }

  const rootHex = request.root;
  if (!rootHex || rootHex.length !== 64) {
    throw new Error('Invalid root: must be 64 hex characters (32 bytes)');
  }

  const rootFelt = hashToFelt(rootHex);

  try {
    const result = await contract.verify_root(rootFelt);
    return {
      ok: true,
      verified: Boolean(result),
      root: rootHex,
    };
  } catch (error) {
    throw new Error(`Verify failed: ${error.message}`);
  }
}

/**
 * Get current blockchain time/block info.
 */
async function handleTime() {
  await initialize();

  try {
    const block = await provider.getBlock('latest');
    return {
      ok: true,
      blockNumber: block.block_number,
      timestamp: block.timestamp,
      blockHash: block.block_hash,
    };
  } catch (error) {
    throw new Error(`Failed to get time: ${error.message}`);
  }
}

/**
 * Get network info.
 */
async function handleNetworkInfo() {
  await initialize();

  try {
    const chainId = await provider.getChainId();
    return {
      ok: true,
      network: config.network,
      rpcUrl: config.rpcUrl,
      chainId: chainId,
      explorerUrl: config.explorerUrl,
      contract: config.contractAddress,
    };
  } catch (error) {
    throw new Error(`Failed to get network info: ${error.message}`);
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
  logDebug('Starting Starknet bridge...');
  logDebug(`Network: ${config.network}`);
  logDebug(`RPC: ${config.rpcUrl}`);
  logDebug(`Contract: ${config.contractAddress || '(not set)'}`);
  logDebug(`Account: ${config.accountAddress ? '(configured)' : '(not set)'}`);

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
    console.error(`[starknet-bridge] Uncaught exception: ${error.message}`);
    process.exit(1);
  });

  process.on('unhandledRejection', (reason) => {
    console.error(`[starknet-bridge] Unhandled rejection: ${reason}`);
  });

  logDebug('Ready for commands');
}

main().catch((error) => {
  console.error(`[starknet-bridge] Fatal error: ${error.message}`);
  process.exit(1);
});
