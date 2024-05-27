include "../../evm-dafny/src/dafny/evm.dfy"
include "../../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module totalSupply {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x01a1(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01a1
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
		st := Push2(st,0x01ac);
		//|fp=0x0060|0x1ac,_,_|
		assume {:axiom} st.IsJumpDest(0x1ac);
		st := JumpI(st);
		if st.PC() == 0x1ac { st := block_0_0x01ac(st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x01ac(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01ac
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x01b4);
		//|fp=0x0060|0x1b4,_|
		st := Push2(st,0x066d);
		//|fp=0x0060|0x66d,0x1b4,_|
		assume {:axiom} st.IsJumpDest(0x66d);
		st := Jump(st);
		st := block_0_0x066d(st);
		return st;
	}

	method block_0_0x01b4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01b4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	{
		var st := st';
		//|fp=0x0060|_,_|
		st := JumpDest(st);
		//|fp=0x0060|_,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,_,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,_,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,_,_|
		st := Dup(st,3);
		//|fp=0x0060|_,0x60,0x60,_,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,_,0x60,0x60,_,_|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,_,_|
		st := Push1(st,0x20);
		st := block_0_0x01be(st);
		return st;
	}

	method block_0_0x01be(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01be
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x60)
	{
		var st := st';
		//|fp=0x0060|0x20,0x60,0x60,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,0x60,0x60,_,_|
		st := Add(st);
		//|fp=0x0060|0x80,0x60,_,_|
		st := Swap(st,2);
		//|fp=0x0060|_,0x60,0x80,_|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,_|
		st := Pop(st);
		//|fp=0x0060|0x80,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,_|
		st := Swap(st,2);
		st := block_0_0x01c7(st);
		return st;
	}

	method block_0_0x01c7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01c7
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(0) == 0x80 && st'.Peek(1) == 0x60)
	{
		var st := st';
		//|fp=0x0060|0x80,0x60,0x60,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,_|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,_|
		st := Return(st);
		return st;
	}

	method block_0_0x066d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x066d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0x1b4)
	{
		var st := st';
		//|fp=0x0060|0x1b4,_|
		st := JumpDest(st);
		//|fp=0x0060|0x1b4,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x1b4,_|
		st := Address(st);
		//|fp=0x0060|_,0x00,0x1b4,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x1b4,_|
		st := AndU160(st);
		//|fp=0x0060|_,0x00,0x1b4,_|
		st := Balance(st);
		//|fp=0x0060|_,0x00,0x1b4,_|
		st := Swap(st,1);
		//|fp=0x0060|0x00,_,0x1b4,_|
		st := Pop(st);
		st := block_0_0x068a(st);
		return st;
	}

	method block_0_0x068a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x068a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x1b4)
	{
		var st := st';
		//|fp=0x0060|_,0x1b4,_|
		st := Swap(st,1);
		//|fp=0x0060|0x1b4,_,_|
		assume {:axiom} st.IsJumpDest(0x1b4);
		st := Jump(st);
		st := block_0_0x01b4(st);
		return st;
	}

}
