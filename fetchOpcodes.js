#!/usr/bin/env node

const { Chain, Hardfork } = require('@ethereumjs/common');
const { EVM } = require('@ethereumjs/evm');

const evm = new EVM({
    chain: Chain.Mainnet,
    hardfork: Hardfork.Merge,
})
console.log(JSON.stringify(Array.from(evm._opcodes.values()), null, 4))
