/**
 * Deploy AnubisAnchor zkApp to Mina
 *
 * Usage:
 *   MINA_PRIVATE_KEY=<key> npm run deploy -- --network mainnet
 *
 * Environment:
 *   MINA_PRIVATE_KEY: Deployer's private key (Base58)
 */
import { Mina, PrivateKey, AccountUpdate, fetchAccount, } from 'o1js';
import { AnubisAnchor } from '../src/index.js';
// Workaround for o1js State binding during compilation
// See: https://github.com/o1-labs/o1js/issues/1677
// Network configurations
const NETWORKS = {
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
async function main() {
    // Parse arguments
    const args = process.argv.slice(2);
    const networkArg = args.find((a) => a.startsWith('--network='))?.split('=')[1]
        || args[args.indexOf('--network') + 1]
        || 'mainnet';
    const network = NETWORKS[networkArg];
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
        networkId: network.networkId,
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
    // Create zkApp instance BEFORE compiling (required for State binding)
    const zkApp = new AnubisAnchor(zkAppAddress);
    // Analyze methods first for better error messages
    console.log('\nAnalyzing methods...');
    await AnubisAnchor.analyzeMethods();
    // Compile contract
    console.log('Compiling AnubisAnchor...');
    const startCompile = Date.now();
    const { verificationKey } = await AnubisAnchor.compile();
    console.log(`Compiled in ${(Date.now() - startCompile) / 1000}s`);
    // Fetch deployer account
    console.log('\nFetching deployer account...');
    await fetchAccount({ publicKey: deployerAddress });
    // Deploy
    console.log('\nCreating deploy transaction...');
    const tx = await Mina.transaction({ sender: deployerAddress, fee: 1_100_000_000 }, // 1.1 MINA (includes account creation)
    async () => {
        AccountUpdate.fundNewAccount(deployerAddress);
        await zkApp.deploy({ verificationKey });
    });
    console.log('Proving transaction...');
    await tx.prove();
    console.log('Signing transaction...');
    tx.sign([deployer, zkAppKey]);
    console.log('Sending transaction...');
    const pendingTx = await tx.send();
    if (pendingTx.status !== 'pending') {
        console.error('Transaction failed to send!');
        process.exit(1);
    }
    console.log(`\nTransaction sent: ${pendingTx.hash}`);
    console.log('Waiting for inclusion (this may take a few minutes)...');
    try {
        await pendingTx.wait();
        console.log('Transaction included!');
    }
    catch (e) {
        console.log('Wait timed out, but transaction may still be included.');
    }
    // Summary
    console.log('\n========================================');
    console.log('DEPLOYMENT COMPLETE');
    console.log('========================================');
    console.log(`Network: ${networkArg}`);
    console.log(`zkApp Address: ${zkAppAddress.toBase58()}`);
    console.log(`zkApp Private Key: ${zkAppKey.toBase58()}`);
    console.log(`Transaction: ${pendingTx.hash}`);
    console.log('\nSave these for use with Anubis Notary:');
    console.log(`  export MINA_ZKAPP_ADDRESS=${zkAppAddress.toBase58()}`);
    console.log('========================================');
}
main().catch((error) => {
    console.error('Deployment failed:', error);
    process.exit(1);
});
//# sourceMappingURL=deploy.js.map