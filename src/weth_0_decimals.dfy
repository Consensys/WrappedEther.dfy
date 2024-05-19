include "../../evm-dafny/src/dafny/evm.dfy"
include "../../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module decimals {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x0266(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0266
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
		st := Push2(st,0x0271);
		//|fp=0x0060|0x271,_,_|
		assume st.IsJumpDest(0x271);
		st := JumpI(st);
		if st.PC() == 0x271 { st := block_0_0x0271(st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x0271(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0271
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x0279);
		//|fp=0x0060|0x279,_|
		st := Push2(st,0x0b05);
		//|fp=0x0060|0xb05,0x279,_|
		assume st.IsJumpDest(0xb05);
		st := Jump(st);
		st := block_0_0x0b05(st);
		return st;
	}

	method block_0_0x0279(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0279
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	{
		var st := st';
		//|fp=0x0060|_,0x279,_|
		st := JumpDest(st);
		//|fp=0x0060|_,0x279,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,_,0x279,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,_,0x279,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,_,0x279,_|
		st := Dup(st,3);
		//|fp=0x0060|_,0x60,0x60,_,0x279,_|
		st := Push1(st,0xff);
		//|fp=0x0060|0xff,_,0x60,0x60,_,0x279,_|
		st := AndU8(st);
		//|fp=0x0060|_,0x60,0x60,_,0x279,_|
		st := Push1(st,0xff);
		st := block_0_0x0284(st);
		return st;
	}

	method block_0_0x0284(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0284
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(2) == 0x60)
	{
		var st := st';
		//|fp=0x0060|0xff,_,0x60,0x60,_,0x279,_|
		st := AndU8(st);
		//|fp=0x0060|_,0x60,0x60,_,0x279,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,_,0x60,0x60,_,0x279,_|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,_,0x279,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,_,0x279,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,0x60,0x60,_,0x279,_|
		st := Add(st);
		//|fp=0x0060|0x80,0x60,_,0x279,_|
		st := Swap(st,2);
		//|fp=0x0060|_,0x60,0x80,0x279,_|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0x279,_|
		st := Pop(st);
		st := block_0_0x028d(st);
		return st;
	}

	method block_0_0x028d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x028d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == 0x80)
	{
		var st := st';
		//|fp=0x0060|0x80,0x279,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0x279,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0x279,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0x279,_|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,0x279,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,0x279,_|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0x279,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0x279,_|
		st := Return(st);
		return st;
	}

	method block_0_0x0b05(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b05
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0x279)
	{
		var st := st';
		//|fp=0x0060|0x279,_|
		st := JumpDest(st);
		//|fp=0x0060|0x279,_|
		st := Push1(st,0x02);
		//|fp=0x0060|0x02,0x279,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x02,0x279,_|
		st := Swap(st,1);
		//|fp=0x0060|0x02,0x00,0x279,_|
		st := SLoad(st);
		//|fp=0x0060|_,0x00,0x279,_|
		st := Swap(st,1);
		//|fp=0x0060|0x00,_,0x279,_|
		st := Push2(st,0x0100);
		//|fp=0x0060|0x100,0x00,_,0x279,_|
		st := Exp(st);
		st := block_0_0x0b11(st);
		return st;
	}

	method block_0_0x0b11(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b11
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x279)
	{
		var st := st';
		//|fp=0x0060|_,_,0x279,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,0x279,_|
		st := Div(st);
		//|fp=0x0060|_,0x279,_|
		st := Push1(st,0xff);
		//|fp=0x0060|0xff,_,0x279,_|
		st := AndU8(st);
		//|fp=0x0060|_,0x279,_|
		st := Dup(st,2);
		//|fp=0x0060|0x279,_,0x279,_|
		assume st.IsJumpDest(0x279);
		st := Jump(st);
		st := block_0_0x0279(st);
		return st;
	}

}
