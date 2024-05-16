include "../../evm-dafny/src/dafny/evm.dfy"
include "../../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module balanceOf {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x0295(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0295
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
		st := Push2(st,0x02a0);
		//|fp=0x0060|0x2a0*,_,_|
		assume st.IsJumpDest(0x2a0);
		st := JumpI(st);
		if st.PC() == 0x2a0 { st := block_0_0x02a0(st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|_,_|
		st := Dup(st,1);
		//|fp=0x0060|_,_,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x02a0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02a0
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x02cc);
		//|fp=0x0060|0x2cc*,_|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04*,0x2cc*,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04*,_,0x2cc*,_|
		st := Dup(st,1);
		//|fp=0x0060|_,0x04*,_,0x2cc*,_|
		st := CallDataLoad(st);
		//|fp=0x0060|_,0x04*,_,0x2cc*,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|_,_,0x04*,_,0x2cc*,_|
		st := And(st);
		st := block_0_0x02bf(st);
		return st;
	}

	method block_0_0x02bf(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02bf
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(1) == 0x4 && st'.Peek(3) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|_,0x04*,_,0x2cc*,_|
		st := Swap(st,1);
		//|fp=0x0060|0x04*,_,_,0x2cc*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,0x04*,_,_,0x2cc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|_,_,_,_,0x2cc*,_|
		st := Add(st);
		//|fp=0x0060|_,_,_,0x2cc*,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,_,0x2cc*,_|
		st := Swap(st,2);
		//|fp=0x0060|_,_,_,0x2cc*,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,_,0x2cc*,_|
		st := Pop(st);
		//|fp=0x0060|_,_,0x2cc*,_|
		st := Pop(st);
		st := block_0_0x02c8(st);
		return st;
	}

	method block_0_0x02c8(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02c8
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|_,0x2cc*,_|
		st := Push2(st,0x0b18);
		//|fp=0x0060|0xb18*,_,0x2cc*,_|
		assume st.IsJumpDest(0xb18);
		st := Jump(st);
		st := block_0_0x0b18(st);
		return st;
	}

	method block_0_0x02cc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02cc
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	{
		var st := st';
		//|fp=0x0060|_,_,_|
		st := JumpDest(st);
		//|fp=0x0060|_,_,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40*,_,_,_|
		st := MLoad(st);
		//|fp=0x0060|0x60*,_,_,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60*,_,_,_,_|
		st := Dup(st,3);
		//|fp=0x0060|_,0x60*,_,_,_,_|
		st := Dup(st,2);
		//|fp=0x0060|_,_,0x60*,_,_,_,_|
		st := MStore(st);
		//|fp=0x0060|0x60*,_,_,_,_|
		st := Push1(st,0x20);
		st := block_0_0x02d6(st);
		return st;
	}

	method block_0_0x02d6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02d6
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x60)
	{
		var st := st';
		//|fp=0x0060|0x20*,0x60*,_,_,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20*,0x60*,_,_,_,_|
		st := Add(st);
		//|fp=0x0060|0x80*,_,_,_,_|
		st := Swap(st,2);
		//|fp=0x0060|_,_,0x80*,_,_|
		st := Pop(st);
		//|fp=0x0060|_,0x80*,_,_|
		st := Pop(st);
		//|fp=0x0060|0x80*,_,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40*,0x80*,_,_|
		st := MLoad(st);
		//|fp=0x0060|0x60*,0x80*,_,_|
		st := Dup(st,1);
		//|fp=0x0060|_,0x60*,0x80*,_,_|
		st := Swap(st,2);
		st := block_0_0x02df(st);
		return st;
	}

	method block_0_0x02df(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02df
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == 0x80 && st'.Peek(1) == 0x60)
	{
		var st := st';
		//|fp=0x0060|0x80*,0x60*,_,_,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|_,_,_,_,_|
		st := Sub(st);
		//|fp=0x0060|_,_,_,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,_,_|
		st := Return(st);
		return st;
	}

	method block_0_0x0b18(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b18
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|_,0x2cc*,_|
		st := JumpDest(st);
		//|fp=0x0060|_,0x2cc*,_|
		st := Push1(st,0x03);
		//|fp=0x0060|_,_,0x2cc*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|_,_,_,0x2cc*,_|
		st := MStore(st);
		//|fp=0x0060|_,0x2cc*,_|
		st := Dup(st,1);
		//|fp=0x0060|_,_,0x2cc*,_|
		st := Push1(st,0x00);
		//|fp=0x0060|_,_,_,0x2cc*,_|
		st := MStore(st);
		//|fp=0x0060|_,0x2cc*,_|
		st := Push1(st,0x40);
		st := block_0_0x0b24(st);
		return st;
	}

	method block_0_0x0b24(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b24
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|_,_,0x2cc*,_|
		st := Push1(st,0x00);
		//|fp=0x0060|_,_,_,0x2cc*,_|
		st := Keccak256(st);
		//|fp=0x0060|_,_,0x2cc*,_|
		st := Push1(st,0x00);
		//|fp=0x0060|_,_,_,0x2cc*,_|
		st := Swap(st,2);
		//|fp=0x0060|_,_,_,0x2cc*,_|
		st := Pop(st);
		//|fp=0x0060|_,_,0x2cc*,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,0x2cc*,_|
		st := Pop(st);
		//|fp=0x0060|_,0x2cc*,_|
		st := SLoad(st);
		st := block_0_0x0b2e(st);
		return st;
	}

	method block_0_0x0b2e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b2e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|_,0x2cc*,_|
		st := Dup(st,2);
		//|fp=0x0060|0x2cc*,_,_,_|
		assume st.IsJumpDest(0x2cc);
		st := Jump(st);
		st := block_0_0x02cc(st);
		return st;
	}

}
