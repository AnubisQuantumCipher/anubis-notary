/**
 * Interact with AnubisAnchor zkApp
 *
 * Usage:
 *   MINA_PRIVATE_KEY=<key> npm run interact -- --action anchor --root <hex>
 *   npm run interact -- --action verify --root <hex>
 *   npm run interact -- --action status
 *
 * Environment:
 *   MINA_PRIVATE_KEY: User's private key (Base58)
 *   MINA_ZKAPP_ADDRESS: Deployed zkApp address
 *   MINA_NETWORK: Network (mainnet, devnet, local)
 */

import {
  Mina,
  PrivateKey,
  PublicKey,
  fetchAccount,
} from 'o1js';
import { AnubisAnchor, hexToField } from '../src/index.js';

// Network configurations
const NETWORKS: Record<string, { mina: string; networkId: 'mainnet' | 'testnet' }> = {
  mainnet: {
    mina: 'https://api.minascan.io/node/mainnet/v1/graphql',
    networkId: 'mainnet',
  },
  devnet: {
    mina: 'https://api.minascan.io/node/devnet/v1/graphql',
    networkId: 'testnet',
  },
  local: {
    mina: 'http://localhost:8080/graphql',
    networkId: 'testnet',
  },
};

function parseArgs() {
  const args = process.argv.slice(2);
  const result: Record<string, string> = {};

  for (let i = 0; i < args.length; i++) {
    if (args[i].startsWith('--')) {
      const key = args[i].slice(2);
      if (args[i].includes('=')) {
        const [k, v] = args[i].slice(2).split('=');
        result[k] = v;
      } else if (i + 1 < args.length && !args[i + 1].startsWith('--')) {
        result[key] = args[i + 1];
        i++;
      } else {
        result[key] = 'true';
      }
    }
  }

  return result;
}

async function main() {
  const args = parseArgs();
  const action = args.action || 'status';
  const networkName = args.network || process.env.MINA_NETWORK || 'mainnet';
  const zkAppAddressStr = args.address || process.env.MINA_ZKAPP_ADDRESS;

  if (!zkAppAddressStr) {
    console.error('MINA_ZKAPP_ADDRESS required');
    process.exit(1);
  }

  const network = NETWORKS[networkName];
  if (!network) {
    console.error(`Unknown network: ${networkName}`);
    process.exit(1);
  }

  console.log(`Network: ${networkName}`);
  console.log(`zkApp: ${zkAppAddressStr}`);

  // Setup network
  const Network = Mina.Network({
    mina: network.mina,
    networkId: network.networkId,
  });
  Mina.setActiveInstance(Network);

  // Parse addresses
  const zkAppAddress = PublicKey.fromBase58(zkAppAddressStr);
  const zkApp = new AnubisAnchor(zkAppAddress);

  // Compile if needed for actions that require proofs
  if (action === 'anchor') {
    console.log('\nCompiling AnubisAnchor...');
    await AnubisAnchor.compile();
  }

  // Fetch account
  console.log('\nFetching zkApp state...');
  await fetchAccount({ publicKey: zkAppAddress });

  switch (action) {
    case 'status': {
      const merkleRoot = zkApp.merkleRoot.get();
      const anchorCount = zkApp.anchorCount.get();

      console.log('\n========================================');
      console.log('ZKAPP STATUS');
      console.log('========================================');
      console.log(`Address: ${zkAppAddressStr}`);
      console.log(`Anchor Count: ${anchorCount.toString()}`);
      console.log(`Current Root: ${merkleRoot.toString()}`);
      console.log('========================================');
      break;
    }

    case 'anchor': {
      const privateKey = process.env.MINA_PRIVATE_KEY;
      if (!privateKey) {
        console.error('MINA_PRIVATE_KEY required for anchoring');
        process.exit(1);
      }

      const rootHex = args.root;
      if (!rootHex) {
        console.error('--root <hex> required');
        process.exit(1);
      }

      const sender = PrivateKey.fromBase58(privateKey);
      const senderAddress = sender.toPublicKey();
      console.log(`Sender: ${senderAddress.toBase58()}`);

      await fetchAccount({ publicKey: senderAddress });

      const rootField = hexToField(rootHex);
      console.log(`\nAnchoring root: ${rootHex}`);
      console.log(`As Field: ${rootField.toString()}`);

      const tx = await Mina.transaction(
        { sender: senderAddress, fee: 100_000_000 },
        async () => {
          await zkApp.anchorRoot(rootField);
        }
      );

      console.log('\nProving transaction...');
      await tx.prove();

      console.log('Signing transaction...');
      tx.sign([sender]);

      console.log('Sending transaction...');
      const pendingTx = await tx.send();

      if (pendingTx.status !== 'pending') {
        console.error('Transaction failed to send!');
        process.exit(1);
      }

      console.log(`Transaction: ${pendingTx.hash}`);
      console.log('Waiting for inclusion...');

      try {
        await pendingTx.wait();
        console.log('Transaction included!');
      } catch (e) {
        console.log('Wait timed out, but transaction may still be included.');
      }
      break;
    }

    case 'verify': {
      const rootHex = args.root;
      if (!rootHex) {
        console.error('--root <hex> required');
        process.exit(1);
      }

      const rootField = hexToField(rootHex);
      const currentRoot = zkApp.merkleRoot.get();

      const isMatch = rootField.equals(currentRoot).toBoolean();

      console.log('\n========================================');
      console.log('VERIFICATION RESULT');
      console.log('========================================');
      console.log(`Provided Root: ${rootHex}`);
      console.log(`On-Chain Root: ${currentRoot.toString()}`);
      console.log(`Match: ${isMatch ? 'YES' : 'NO'}`);
      console.log('========================================');
      break;
    }

    default:
      console.error(`Unknown action: ${action}`);
      console.error('Available actions: status, anchor, verify');
      process.exit(1);
  }
}

main().catch((error) => {
  console.error('Error:', error);
  process.exit(1);
});
