include "../../evm-dafny/src/dafny/evm.dfy"
include "../../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"
include "weth_0_util.dfy"

module transfer {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header
	import opened util

	method block_0_0x0370(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0370
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := CallValue(st);
		//|fp=0x0060|_,_|
		st := IsZero(st);
		//|fp=0x0060|_,_|
		st := Push2(st,0x037b);
		//|fp=0x0060|0x37b,_,_|
		assume {:axiom} st.IsJumpDest(0x37b);
		st := JumpI(st);
		if st.PC() == 0x37b { st := block_0_0x037b(st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x037b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x037b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x03b0);
		//|fp=0x0060|0x3b0,_|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,0x3b0,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x3b0,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x04,0x3b0,_|
		st := CallDataLoad(st);
		//|fp=0x0060|_,0x04,0x04,0x3b0,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x04,0x04,0x3b0,_|
		st := AndU160(st);
		st := block_0_0x039a(st);
		return st;
	}

	method block_0_0x039a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x039a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(1) == 0x4 && st'.Peek(3) == 0x3b0)
	{
		var st := st';
		//|fp=0x0060|_,0x04,0x04,0x3b0,_|
		st := Swap(st,1);
		//|fp=0x0060|0x04,_,0x04,0x3b0,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,_,0x04,0x3b0,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,0x04,_,0x04,0x3b0,_|
		st := Add(st);
		//|fp=0x0060|0x24,_,0x04,0x3b0,_|
		st := Swap(st,1);
		//|fp=0x0060|_,0x24,0x04,0x3b0,_|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,_,0x3b0,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,_,0x3b0,_|
		st := Dup(st,1);
		//|fp=0x0060|0x24,0x24,0x04,_,0x3b0,_|
		st := CallDataLoad(st);
		st := block_0_0x03a3(st);
		return st;
	}

	method block_0_0x03a3(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03a3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(1) == 0x24 && st'.Peek(4) == 0x3b0)
	{
		var st := st';
		//|fp=0x0060|_,0x24,0x04,_,0x3b0,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24,_,0x04,_,0x3b0,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x24,_,0x04,_,0x3b0,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,0x24,_,0x04,_,0x3b0,_|
		st := Add(st);
		//|fp=0x0060|0x44,_,0x04,_,0x3b0,_|
		st := Swap(st,1);
		//|fp=0x0060|_,0x44,0x04,_,0x3b0,_|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x44,_,_,0x3b0,_|
		st := Swap(st,1);
		//|fp=0x0060|0x44,0x04,_,_,0x3b0,_|
		st := Pop(st);
		//|fp=0x0060|0x04,_,_,0x3b0,_|
		st := Pop(st);
		st := block_0_0x03ac(st);
		return st;
	}

	method block_0_0x03ac(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03ac
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x3b0)
	{
		var st := st';
		//|fp=0x0060|_,_,0x3b0,_|
		st := Push2(st,0x0bce);
		//|fp=0x0060|0xbce,_,_,0x3b0,_|
		assume {:axiom} st.IsJumpDest(0xbce);
		st := Jump(st);
		st := block_0_0x0bce(st);
		return st;
	}

	method block_0_0x0bce(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bce
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x3b0)
	{
		var st := st';
		//|fp=0x0060|_,_,0x3b0,_|
		st := JumpDest(st);
		//|fp=0x0060|_,_,0x3b0,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_,_,0x3b0,_|
		st := Push2(st,0x0bdb);
		//|fp=0x0060|0xbdb,0x00,_,_,0x3b0,_|
		st := Caller(st);
		//|fp=0x0060|_,0xbdb,0x00,_,_,0x3b0,_|
		st := Dup(st,5);
		//|fp=0x0060|_,_,0xbdb,0x00,_,_,0x3b0,_|
		st := Dup(st,5);
		//|fp=0x0060|_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		st := Push2(st,0x068c);
		//|fp=0x0060|0x68c,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		assume {:axiom} st.IsJumpDest(0x68c);
		st := Jump(st);
		st := block_0_0x068c(st);
		return st;
	}

}
