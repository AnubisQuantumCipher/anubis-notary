/**
 * Deploy AnubisAnchor zkApp to Mina
 *
 * Usage:
 *   MINA_PRIVATE_KEY=<key> npm run deploy -- --network devnet
 *
 * Environment:
 *   MINA_PRIVATE_KEY: Deployer's private key (Base58)
 *   MINA_NETWORK: Network to deploy to (mainnet, devnet, local)
 */

import {
  Mina,
  PrivateKey,
  PublicKey,
  AccountUpdate,
  fetchAccount,
} from 'o1js';
import { AnubisAnchor } from '../src/index.js';

// Network configurations
const NETWORKS = {
  mainnet: {
    mina: 'https://graphql.minaexplorer.com',
    archive: 'https://archive.minaexplorer.com',
  },
  devnet: {
    mina: 'https://devnet.minaexplorer.com/graphql',
    archive: 'https://devnet-archive.minaexplorer.com',
  },
  local: {
    mina: 'http://localhost:8080/graphql',
    archive: 'http://localhost:8081',
  },
};

async function main() {
  // Parse arguments
  const args = process.argv.slice(2);
  const networkArg = args.find((a) => a.startsWith('--network='))?.split('=')[1]
    || args[args.indexOf('--network') + 1]
    || 'devnet';

  const network = NETWORKS[networkArg as keyof typeof NETWORKS];
  if (!network) {
    console.error(`Unknown network: ${networkArg}`);
    console.error('Available networks: mainnet, devnet, local');
    process.exit(1);
  }

  console.log(`Deploying to ${networkArg}...`);
  console.log(`GraphQL: ${network.mina}`);

  // Get deployer key
  const deployerKey = process.env.MINA_PRIVATE_KEY;
  if (!deployerKey) {
    console.error('MINA_PRIVATE_KEY environment variable required');
    process.exit(1);
  }

  // Setup network
  const Network = Mina.Network({
    mina: network.mina,
    archive: network.archive,
  });
  Mina.setActiveInstance(Network);

  // Parse keys
  const deployer = PrivateKey.fromBase58(deployerKey);
  const deployerAddress = deployer.toPublicKey();
  console.log(`Deployer: ${deployerAddress.toBase58()}`);

  // Generate new zkApp keypair
  const zkAppKey = PrivateKey.random();
  const zkAppAddress = zkAppKey.toPublicKey();
  console.log(`zkApp Address: ${zkAppAddress.toBase58()}`);
  console.log(`zkApp Private Key: ${zkAppKey.toBase58()}`);

  // Compile contract
  console.log('\nCompiling AnubisAnchor...');
  const startCompile = Date.now();
  const { verificationKey } = await AnubisAnchor.compile();
  console.log(`Compiled in ${(Date.now() - startCompile) / 1000}s`);
  console.log(`Verification Key Hash: ${verificationKey.hash.toString().slice(0, 20)}...`);

  // Fetch deployer account
  console.log('\nFetching deployer account...');
  await fetchAccount({ publicKey: deployerAddress });

  // Create zkApp instance
  const zkApp = new AnubisAnchor(zkAppAddress);

  // Deploy
  console.log('\nCreating deploy transaction...');
  const tx = await Mina.transaction(
    { sender: deployerAddress, fee: 100_000_000 }, // 0.1 MINA
    async () => {
      AccountUpdate.fundNewAccount(deployerAddress);
      await zkApp.deploy({ verificationKey });
      await zkApp.initialize(deployerAddress);
    }
  );

  console.log('Proving transaction...');
  await tx.prove();

  console.log('Signing transaction...');
  tx.sign([deployer, zkAppKey]);

  console.log('Sending transaction...');
  const pendingTx = await tx.send();

  if (!pendingTx.isSuccess) {
    console.error('Transaction failed!');
    process.exit(1);
  }

  console.log(`\nTransaction sent: ${pendingTx.hash}`);
  console.log('Waiting for inclusion...');

  const includedTx = await pendingTx.wait();
  console.log(`Included in block: ${includedTx.blockHeight}`);

  // Summary
  console.log('\n========================================');
  console.log('DEPLOYMENT SUCCESSFUL');
  console.log('========================================');
  console.log(`Network: ${networkArg}`);
  console.log(`zkApp Address: ${zkAppAddress.toBase58()}`);
  console.log(`Transaction: ${pendingTx.hash}`);
  console.log(`Block: ${includedTx.blockHeight}`);
  console.log('\nSave the zkApp address for use with Anubis Notary:');
  console.log(`  export MINA_ZKAPP_ADDRESS=${zkAppAddress.toBase58()}`);
  console.log('========================================');
}

main().catch((error) => {
  console.error('Deployment failed:', error);
  process.exit(1);
});
