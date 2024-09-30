include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"
include "weth_0_util.dfy"

module deposit {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header
	import opened util

	method block_0_0x03ca(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03ca
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires st'.evm.stack.contents == [st'.Peek(0)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xd0e30db0|
		st := JumpDest(st);
		//|fp=0x0060|0xd0e30db0|
		st := Push2(st,0x03d2);
		//|fp=0x0060|0x3d2,0xd0e30db0|
		st := Push2(st,0x0440);
		//|fp=0x0060|0x440,0x3d2,0xd0e30db0|
		assume {:axiom} st.IsJumpDest(0x440);
		st := Jump(st);
		//|fp=0x0060|0x3d2,0xd0e30db0|
		stackLemma(st,st.Operands());
		st := block_1_0x0440(st);
		return st;
	}

}
