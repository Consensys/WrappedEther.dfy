include "../../evm-dafny/src/dafny/evm.dfy"
include "../../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module name {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x00b9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00b9
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
		st := Push2(st,0x00c4);
		//|fp=0x0060|0xc4*,_,_|
		assume st.IsJumpDest(0xc4);
		st := JumpI(st);
		if st.PC() == 0xc4 { st := block_0_0x00c4(st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|_,_|
		st := Dup(st,1);
		//|fp=0x0060|_,_,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x00c4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00c4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x00cc);
		//|fp=0x0060|0xcc*,_|
		st := Push2(st,0x04dd);
		//|fp=0x0060|0x4dd*,0xcc*,_|
		assume st.IsJumpDest(0x4dd);
		st := Jump(st);
		st := block_0_0x04dd(st);
		return st;
	}

	method block_0_0x00cc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00cc
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == 0x60)
	{
		var st := st';
		//||0x60*,_,_|
		st := JumpDest(st);
		//||0x60*,_,_|
		st := Push1(st,0x40);
		//||0x40*,0x60*,_,_|
		st := MLoad(st);
		//||_*,0x60*,_,_|
		st := Dup(st,1);
		//||_*,_*,0x60*,_,_|
		st := Dup(st,1);
		//||_*,_,_*,0x60*,_,_|
		st := Push1(st,0x20);
		//||0x20*,_*,_,_*,0x60*,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20*,_*,_,_*,0x60*,_,_|
		st := Add(st);
		//||_*,_,_*,0x60*,_,_|
		st := Dup(st,3);
		st := block_0_0x00d6(st);
		return st;
	}

	method block_0_0x00d6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00d6
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(4) == 0x60)
	{
		var st := st';
		//||_*,_*,_,_,0x60*,_,_|
		st := Dup(st,2);
		//||_*,_*,_*,_,_,0x60*,_,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,_,_*,_,_,0x60*,_,_|
		st := Sub(st);
		//||_,_*,_,_,0x60*,_,_|
		st := Dup(st,3);
		//||_,_,_*,_,_,0x60*,_,_|
		st := MStore(st);
		//||_*,_,_,0x60*,_,_|
		st := Dup(st,4);
		//||0x60*,_*,_,_,_,_,_|
		st := Dup(st,2);
		//||_*,0x60*,_,_,_,_,_,_|
		st := Dup(st,2);
		//||_,_*,0x60*,_,_,_,_,_,_|
		st := MLoad(st);
		st := block_0_0x00de(st);
		return st;
	}

	method block_0_0x00de(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00de
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x60)
	{
		var st := st';
		//||_,_*,0x60*,_,_,_,_,_,_|
		st := Dup(st,2);
		//||_,_,_*,0x60*,_,_,_,_,_,_|
		st := MStore(st);
		//||_*,0x60*,_,_,_,_,_,_|
		st := Push1(st,0x20);
		//||0x20*,_*,0x60*,_,_,_,_,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20*,_*,0x60*,_,_,_,_,_,_|
		st := Add(st);
		//||_*,0x60*,_,_,_,_,_,_|
		st := Swap(st,2);
		//||_,0x60*,_*,_,_,_,_,_|
		st := Pop(st);
		//||0x60*,_*,_,_,_,_,_|
		st := Dup(st,1);
		//||0x60*,0x60*,_*,_,_,_,_,_|
		st := MLoad(st);
		st := block_0_0x00e7(st);
		return st;
	}

	method block_0_0x00e7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00e7
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(1) == 0x60)
	{
		var st := st';
		//||_*,0x60*,_*,_,_,_,_,_|
		st := Swap(st,1);
		//||0x60*,_*,_*,_,_,_,_,_|
		st := Push1(st,0x20);
		//||0x20*,0x60*,_*,_*,_,_,_,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20*,0x60*,_*,_*,_,_,_,_,_|
		st := Add(st);
		//||0x80*,_*,_*,_,_,_,_,_|
		st := Swap(st,1);
		//||_*,0x80*,_*,_,_,_,_,_|
		st := Dup(st,1);
		//||_,_*,0x80*,_*,_,_,_,_,_|
		st := Dup(st,4);
		//||_*,_,_*,0x80*,_*,_,_,_,_,_|
		st := Dup(st,4);
		//||0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Push1(st,0x00);
		st := block_0_0x00f1(st);
		return st;
	}

	method block_0_0x00f1(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00f1
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires (st'.Peek(1) == 0x80)
	{
		var st := st';
		//||0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := JumpDest(st);
		//||0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Dup(st,4);
		//||_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Dup(st,2);
		//||_,_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Lt(st);
		//||_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := IsZero(st);
		//||_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Push2(st,0x010c);
		//||0x10c*,_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||0x10c*,_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		assume st.IsJumpDest(0x10c);
		st := JumpI(st);
		if st.PC() == 0x10c { st := block_0_0x010c(st); return st;}
		//||0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Dup(st,1);
		st := block_0_0x00fb(st);
		return st;
	}

	method block_0_0x00fb(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00fb
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires (st'.Peek(2) == 0x80)
	{
		var st := st';
		//||0x00*,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Dup(st,3);
		//||0x80*,0x00*,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||0x80*,_*,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_,_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Add(st);
		//||_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := MLoad(st);
		//||_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Dup(st,2);
		//||0x00*,_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Dup(st,5);
		//||_*,0x00*,_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,_*,_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_,_,_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_,_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Add(st);
		//||_,_,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := MStore(st);
		//||0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Push1(st,0x20);
		st := block_0_0x0104(st);
		return st;
	}

	method block_0_0x0104(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0104
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(2) == 0x80)
	{
		var st := st';
		//||0x20*,0x00*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||0x20*,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Dup(st,2);
		//||0x00*,0x20*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,0x20*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		// Havoc 0
		//||_*,0x20*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,0x20*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_*,0x20*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,0x20*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Add(st);
		//||_*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		// Havoc 0
		//||_*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_*,_,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Swap(st,1);
		//||_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		//||_,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Pop(st);
		//||_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		st := Push2(st,0x00f1);
		//||0xf1*,_*,0x80*,_*,_,_*,_,_*,_,_,_,_,_|
		assume st.IsJumpDest(0xf1);
		st := Jump(st);
		st := block_0_0x00f1(st);
		return st;
	}

	method block_0_0x010c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x010c
	// Stack height(s)
	requires st'.Operands() == 12
	{
		var st := st';
		//||_,_,_,_,_*,_,_*,_,_,_,_,_|
		//||_,_,_,_,_*,_,_*,_,_,_,_,_|
		st := JumpDest(st);
		//||_,_,_,_,_*,_,_*,_,_,_,_,_|
		//||_,_,_,_,_*,_,_*,_,_,_,_,_|
		st := Pop(st);
		//||_,_,_,_*,_,_*,_,_,_,_,_|
		st := Pop(st);
		//||_,_,_*,_,_*,_,_,_,_,_|
		st := Pop(st);
		//||_,_*,_,_*,_,_,_,_,_|
		st := Pop(st);
		//||_*,_,_*,_,_,_,_,_|
		st := Swap(st,1);
		//||_,_*,_*,_,_,_,_,_|
		st := Pop(st);
		//||_*,_*,_,_,_,_,_|
		st := Swap(st,1);
		st := block_0_0x0114(st);
		return st;
	}

	method block_0_0x0114(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0114
	// Stack height(s)
	requires st'.Operands() == 7
	{
		var st := st';
		//||_*,_*,_,_,_,_,_|
		st := Dup(st,2);
		//||_*,_*,_*,_,_,_,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_*,_*,_*,_,_,_,_,_|
		st := Add(st);
		//||_*,_*,_,_,_,_,_|
		st := Swap(st,1);
		//||_*,_*,_,_,_,_,_|
		st := Push1(st,0x1f);
		//||0x1f*,_*,_*,_,_,_,_,_|
		st := And(st);
		//||_*,_*,_,_,_,_,_|
		st := Dup(st,1);
		//||_,_*,_*,_,_,_,_,_|
		st := IsZero(st);
		//||_,_*,_*,_,_,_,_,_|
		st := Push2(st,0x0139);
		st := block_0_0x011f(st);
		return st;
	}

	method block_0_0x011f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x011f
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(0) == 0x139)
	{
		var st := st';
		//||0x139*,_,_*,_*,_,_,_,_,_|
		assume st.IsJumpDest(0x139);
		st := JumpI(st);
		if st.PC() == 0x139 { st := block_0_0x0139(st); return st;}
		//||_*,_*,_,_,_,_,_|
		st := Dup(st,1);
		//||_*,_*,_*,_,_,_,_,_|
		st := Dup(st,3);
		//||_*,_*,_*,_,_,_,_,_,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_*,_*,_*,_,_,_,_,_,_|
		st := Sub(st);
		//||_*,_*,_,_,_,_,_,_|
		st := Dup(st,1);
		//||_,_*,_*,_,_,_,_,_,_|
		st := MLoad(st);
		//||_,_*,_*,_,_,_,_,_,_|
		st := Push1(st,0x01);
		//||0x01*,_,_*,_*,_,_,_,_,_,_|
		st := Dup(st,4);
		st := block_0_0x0128(st);
		return st;
	}

	method block_0_0x0128(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0128
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(1) == 0x1)
	{
		var st := st';
		//||_*,0x01*,_,_*,_,_,_,_,_,_,_|
		st := Push1(st,0x20);
		//||0x20*,_*,0x01*,_,_*,_,_,_,_,_,_,_|
		assert st.Peek(1) <= st.Peek(0);
		//||0x20*,_*,0x01*,_,_*,_,_,_,_,_,_,_|
		st := Sub(st);
		//||_*,0x01*,_,_*,_,_,_,_,_,_,_|
		st := Push2(st,0x0100);
		//||0x100*,_*,0x01*,_,_*,_,_,_,_,_,_,_|
		st := Exp(st);
		//||_*,0x01*,_,_*,_,_,_,_,_,_,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,_,_,_*,_,_,_,_,_,_,_|
		st := Sub(st);
		//||_,_,_*,_,_,_,_,_,_,_|
		st := Not(st);
		//||_,_,_*,_,_,_,_,_,_,_|
		st := And(st);
		//||_,_*,_,_,_,_,_,_,_|
		st := Dup(st,2);
		st := block_0_0x0133(st);
		return st;
	}

	method block_0_0x0133(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0133
	// Stack height(s)
	requires st'.Operands() == 10
	{
		var st := st';
		//||_,_,_*,_,_,_,_,_,_,_|
		st := MStore(st);
		//||_*,_,_,_,_,_,_,_|
		st := Push1(st,0x20);
		//||0x20*,_*,_,_,_,_,_,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20*,_*,_,_,_,_,_,_,_|
		st := Add(st);
		//||_*,_,_,_,_,_,_,_|
		st := Swap(st,2);
		//||_,_,_*,_,_,_,_,_|
		st := Pop(st);
		st := block_0_0x0139(st);
		return st;
	}

	method block_0_0x0139(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0139
	// Stack height(s)
	requires st'.Operands() == 7
	{
		var st := st';
		//||_,_*,_,_,_,_,_|
		st := JumpDest(st);
		//||_,_*,_,_,_,_,_|
		st := Pop(st);
		//||_*,_,_,_,_,_|
		st := Swap(st,3);
		//||_,_,_,_*,_,_|
		st := Pop(st);
		//||_,_,_*,_,_|
		st := Pop(st);
		//||_,_*,_,_|
		st := Pop(st);
		//||_*,_,_|
		st := Push1(st,0x40);
		//||0x40*,_*,_,_|
		st := MLoad(st);
		st := block_0_0x0142(st);
		return st;
	}

	method block_0_0x0142(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0142
	// Stack height(s)
	requires st'.Operands() == 4
	{
		var st := st';
		//||_*,_*,_,_|
		st := Dup(st,1);
		//||_,_*,_*,_,_|
		st := Swap(st,2);
		//||_*,_*,_,_,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,_,_,_,_|
		st := Sub(st);
		//||_,_,_,_|
		st := Swap(st,1);
		//||_,_,_,_|
		st := Return(st);
		return st;
	}

	method block_0_0x04dd(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04dd
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0xcc)
	{
		var st := st';
		//|fp=0x0060|0xcc*,_|
		st := JumpDest(st);
		//|fp=0x0060|0xcc*,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00*,0xcc*,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00*,0x00*,0xcc*,_|
		st := SLoad(st);
		//|fp=0x0060|_*,0x00*,0xcc*,_|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01*,_*,0x00*,0xcc*,_|
		st := Dup(st,2);
		//|fp=0x0060|_*,0x01*,_*,0x00*,0xcc*,_|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01*,_*,0x01*,_*,0x00*,0xcc*,_|
		st := And(st);
		st := block_0_0x04e8(st);
		return st;
	}

	method block_0_0x04e8(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04e8
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(1) == 0x1 && st'.Peek(3) == 0x0 && st'.Peek(4) == 0xcc)
	{
		var st := st';
		//|fp=0x0060|_*,0x01*,_*,0x00*,0xcc*,_|
		st := IsZero(st);
		//|fp=0x0060|_*,0x01*,_*,0x00*,0xcc*,_|
		st := Push2(st,0x0100);
		//|fp=0x0060|0x100*,_*,0x01*,_*,0x00*,0xcc*,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x100*,_*,0x01*,_*,0x00*,0xcc*,_|
		st := Mul(st);
		//|fp=0x0060|_*,0x01*,_*,0x00*,0xcc*,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|_*,0x01*,_*,0x00*,0xcc*,_|
		st := Sub(st);
		//|fp=0x0060|_*,_*,0x00*,0xcc*,_|
		st := And(st);
		//|fp=0x0060|_*,0x00*,0xcc*,_|
		st := Push1(st,0x02);
		//|fp=0x0060|0x02*,_*,0x00*,0xcc*,_|
		st := Swap(st,1);
		//|fp=0x0060|_*,0x02*,0x00*,0xcc*,_|
		st := Div(st);
		st := block_0_0x04f3(st);
		return st;
	}

	method block_0_0x04f3(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04f3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(1) == 0x0 && st'.Peek(2) == 0xcc)
	{
		var st := st';
		//|fp=0x0060|_*,0x00*,0xcc*,_|
		st := Dup(st,1);
		//|fp=0x0060|_*,_,0x00*,0xcc*,_|
		st := Push1(st,0x1f);
		//|fp=0x0060|0x1f*,_*,_,0x00*,0xcc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x1f*,_*,_,0x00*,0xcc*,_|
		st := Add(st);
		//|fp=0x0060|_*,_,0x00*,0xcc*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,_*,_,0x00*,0xcc*,_|
		st := Dup(st,1);
		//|fp=0x0060|0x20*,0x20*,_*,_,0x00*,0xcc*,_|
		st := Swap(st,2);
		//|fp=0x0060|_*,0x20*,0x20*,_,0x00*,0xcc*,_|
		st := Div(st);
		//|fp=0x0060|_*,0x20*,_,0x00*,0xcc*,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|_*,0x20*,_,0x00*,0xcc*,_|
		st := Mul(st);
		st := block_0_0x04fd(st);
		return st;
	}

	method block_0_0x04fd(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04fd
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(2) == 0x0 && st'.Peek(3) == 0xcc)
	{
		var st := st';
		//|fp=0x0060|_*,_,0x00*,0xcc*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,_*,_,0x00*,0xcc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20*,_*,_,0x00*,0xcc*,_|
		st := Add(st);
		//|fp=0x0060|_*,_,0x00*,0xcc*,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40*,_*,_,0x00*,0xcc*,_|
		st := MLoad(st);
		//|fp=0x0060|0x60*,_*,_,0x00*,0xcc*,_|
		st := Swap(st,1);
		//|fp=0x0060|_*,0x60*,_,0x00*,0xcc*,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60*,_*,0x60*,_,0x00*,0xcc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|_,_,0x60*,_,0x00*,0xcc*,_|
		st := Add(st);
		//|fp=0x0060|_,0x60*,_,0x00*,0xcc*,_|
		st := Push1(st,0x40);
		st := block_0_0x0508(st);
		return st;
	}

	method block_0_0x0508(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0508
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(2) == 0x60 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0xcc)
	{
		var st := st';
		//|fp=0x0060|_,_,0x60*,_,0x00*,0xcc*,_|
		st := MStore(st);
		//||0x60*,_,0x00*,0xcc*,_|
		st := Dup(st,1);
		//||0x60*,0x60*,_,0x00*,0xcc*,_|
		st := Swap(st,3);
		//||0x00*,0x60*,_,0x60*,0xcc*,_|
		st := Swap(st,2);
		//||_,0x60*,0x00*,0x60*,0xcc*,_|
		st := Swap(st,1);
		//||0x60*,_,0x00*,0x60*,0xcc*,_|
		st := Dup(st,2);
		//||_,0x60*,_,0x00*,0x60*,0xcc*,_|
		st := Dup(st,2);
		//||_,_,0x60*,_,0x00*,0x60*,0xcc*,_|
		st := MStore(st);
		st := block_0_0x0510(st);
		return st;
	}

	method block_0_0x0510(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0510
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x60 && st'.Peek(4) == 0xcc)
	{
		var st := st';
		//||0x60*,_,0x00*,0x60*,0xcc*,_|
		st := Push1(st,0x20);
		//||0x20*,0x60*,_,0x00*,0x60*,0xcc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20*,0x60*,_,0x00*,0x60*,0xcc*,_|
		st := Add(st);
		//||0x80*,_,0x00*,0x60*,0xcc*,_|
		st := Dup(st,3);
		//||0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Dup(st,1);
		//||0x00*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := SLoad(st);
		//||_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x01);
		//||0x01*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Dup(st,2);
		//||_*,0x01*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x01);
		st := block_0_0x051b(st);
		return st;
	}

	method block_0_0x051b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x051b
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(0) == 0x1 && st'.Peek(2) == 0x1 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0x80 && st'.Peek(8) == 0x60 && st'.Peek(9) == 0xcc)
	{
		var st := st';
		//||0x01*,_*,0x01*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := And(st);
		//||_*,0x01*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := IsZero(st);
		//||_*,0x01*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Push2(st,0x0100);
		//||0x100*,_*,0x01*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		//||0x100*,_*,0x01*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Mul(st);
		//||_*,0x01*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_*,0x01*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Sub(st);
		//||_*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := And(st);
		//||_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x02);
		//||0x02*,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Swap(st,1);
		st := block_0_0x0526(st);
		return st;
	}

	method block_0_0x0526(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0526
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(1) == 0x2 && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	{
		var st := st';
		//||_*,0x02*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Div(st);
		//||_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Dup(st,1);
		//||_,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := IsZero(st);
		//||_,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Push2(st,0x0573);
		//||0x573*,_,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		assume st.IsJumpDest(0x573);
		st := JumpI(st);
		if st.PC() == 0x573 { st := block_0_0x0573(st); return st;}
		//||_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Dup(st,1);
		//||_,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x1f);
		//||_,_,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Lt(st);
		st := block_0_0x0531(st);
		return st;
	}

	method block_0_0x0531(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0531
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	{
		var st := st';
		//||_,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Push2(st,0x0548);
		//||0x548*,_,_*,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		assume st.IsJumpDest(0x548);
		st := JumpI(st);
		if st.PC() == 0x548 { st := block_0_0x0548(st); return st;}
		//||_,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Push2(st,0x0100);
		//||0x100*,_,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Dup(st,1);
		//||0x100*,0x100*,_,0x00*,0x80*,_,_,0x60*,0xcc*,_|
		st := Dup(st,4);
		//||0x00*,0x100*,0x100*,_,_,0x80*,_,_,0x60*,0xcc*,_|
		st := SLoad(st);
		//||_*,0x100*,0x100*,_,_,0x80*,_,_,0x60*,0xcc*,_|
		st := Div(st);
		//||_*,0x100*,_,_,0x80*,_,_,0x60*,0xcc*,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		//||_,_,_,_,0x80*,_,_,0x60*,0xcc*,_|
		st := Mul(st);
		st := block_0_0x053d(st);
		return st;
	}

	method block_0_0x053d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x053d
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(3) == 0x80 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	{
		var st := st';
		//||_,_,_,0x80*,_,_,0x60*,0xcc*,_|
		st := Dup(st,4);
		//||_,_,_,_,0x80*,_,_,0x60*,0xcc*,_|
		st := MStore(st);
		//||_,_,0x80*,_,_,0x60*,0xcc*,_|
		st := Swap(st,2);
		//||0x80*,_,_,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x20);
		//||0x20*,0x80*,_,_,_,_,0x60*,0xcc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_,_,_,_,_,_,0x60*,0xcc*,_|
		st := Add(st);
		//||_,_,_,_,_,0x60*,0xcc*,_|
		st := Swap(st,2);
		//||_,_,_,_,_,0x60*,0xcc*,_|
		st := Push2(st,0x0573);
		//||0x573*,_,_,_,_,_,0x60*,0xcc*,_|
		assume st.IsJumpDest(0x573);
		st := Jump(st);
		st := block_0_0x0573(st);
		return st;
	}

	method block_0_0x0548(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0548
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(2) == 0x80 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		//||_*,_,0x80*,_,_,0x60*,0xcc*,_|
		st := JumpDest(st);
		//||_*,_,0x80*,_,_,0x60*,0xcc*,_|
		st := Dup(st,3);
		//||0x80*,_*,_,0x80*,_,_,0x60*,0xcc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x80*,_*,_,0x80*,_,_,0x60*,0xcc*,_|
		st := Add(st);
		//||_*,_,0x80*,_,_,0x60*,0xcc*,_|
		st := Swap(st,2);
		//||0x80*,_,_*,_,_,0x60*,0xcc*,_|
		st := Swap(st,1);
		//||_,0x80*,_*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x00);
		//||_,_,0x80*,_*,_,_,0x60*,0xcc*,_|
		st := MStore(st);
		//||0x80*,_*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x20);
		st := block_0_0x0552(st);
		return st;
	}

	method block_0_0x0552(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0552
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x80 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		//||0x20*,0x80*,_*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x00);
		//||0x00*,0x20*,0x80*,_*,_,_,0x60*,0xcc*,_|
		st := Keccak256(st);
		//||_*,0x80*,_*,_,_,0x60*,0xcc*,_|
		st := Swap(st,1);
		st := block_0_0x0556(st);
		return st;
	}

	method block_0_0x0556(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0556
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		//||0x80*,_*,_*,_,_,0x60*,0xcc*,_|
		//||_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := JumpDest(st);
		//||0x80*,_*,_*,_,_,0x60*,0xcc*,_|
		//||_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Dup(st,2);
		//||_,0x80*,_*,_*,_,_,0x60*,0xcc*,_|
		//||_,_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := SLoad(st);
		//||_,0x80*,_*,_*,_,_,0x60*,0xcc*,_|
		//||_,_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Dup(st,2);
		//||_,_,0x80*,_*,_*,_,_,0x60*,0xcc*,_|
		//||_,_,_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := MStore(st);
		//||0x80*,_*,_*,_,_,0x60*,0xcc*,_|
		//||_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Swap(st,1);
		//||_*,0x80*,_*,_,_,0x60*,0xcc*,_|
		//||_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x01);
		//||0x01*,_*,0x80*,_*,_,_,0x60*,0xcc*,_|
		//||0x01*,_*,_*,_*,_,_,0x60*,0xcc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x01*,_*,0x80*,_*,_,_,0x60*,0xcc*,_|
		//||0x01*,_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Add(st);
		st := block_0_0x055f(st);
		return st;
	}

	method block_0_0x055f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x055f
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		//||_*,0x80*,_*,_,_,0x60*,0xcc*,_|
		//||_*,_*,_*,_,_,0x60*,0xcc*,_|
		// Havoc 0
		//||_*,0x80*,_*,_,_,0x60*,0xcc*,_|
		//||_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Swap(st,1);
		//||0x80*,_*,_*,_,_,0x60*,0xcc*,_|
		//||_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x20);
		//||0x20*,0x80*,_*,_*,_,_,0x60*,0xcc*,_|
		//||0x20*,_*,_*,_*,_,_,0x60*,0xcc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20*,0x80*,_*,_*,_,_,0x60*,0xcc*,_|
		//||0x20*,_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Add(st);
		//||0xa0*,_*,_*,_,_,0x60*,0xcc*,_|
		//||_*,_*,_*,_,_,0x60*,0xcc*,_|
		// Havoc 0
		//||_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Dup(st,1);
		//||_,_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Dup(st,4);
		//||_,_,_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Gt(st);
		st := block_0_0x0566(st);
		return st;
	}

	method block_0_0x0566(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0566
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	{
		var st := st';
		//||_,_*,_*,_*,_,_,0x60*,0xcc*,_|
		st := Push2(st,0x0556);
		//||0x556*,_,_*,_*,_*,_,_,0x60*,0xcc*,_|
		assume st.IsJumpDest(0x556);
		st := JumpI(st);
		if st.PC() == 0x556 { st := block_0_0x0556(st); return st;}
		//||_*,_,_*,_,_,0x60*,0xcc*,_|
		st := Dup(st,3);
		//||_*,_*,_,_*,_,_,0x60*,0xcc*,_|
		st := Swap(st,1);
		//||_*,_*,_,_*,_,_,0x60*,0xcc*,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_*,_*,_,_*,_,_,0x60*,0xcc*,_|
		st := Sub(st);
		//||_*,_,_*,_,_,0x60*,0xcc*,_|
		st := Push1(st,0x1f);
		//||0x1f*,_*,_,_*,_,_,0x60*,0xcc*,_|
		st := And(st);
		//||_*,_,_*,_,_,0x60*,0xcc*,_|
		st := Dup(st,3);
		st := block_0_0x0571(st);
		return st;
	}

	method block_0_0x0571(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0571
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	{
		var st := st';
		//||_*,_*,_,_,_,_,0x60*,0xcc*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_,_,_,_,_,_,0x60*,0xcc*,_|
		st := Add(st);
		//||_,_,_,_,_,0x60*,0xcc*,_|
		st := Swap(st,2);
		st := block_0_0x0573(st);
		return st;
	}

	method block_0_0x0573(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0573
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		//||_,_,_,_,_,0x60*,0xcc*,_|
		//||_,_,_,_,_,0x60*,0xcc*,_|
		//||_,_,_,_,_,0x60*,0xcc*,_|
		st := JumpDest(st);
		//||_,_,_,_,_,0x60*,0xcc*,_|
		//||_,_,_,_,_,0x60*,0xcc*,_|
		//||_,_,_,_,_,0x60*,0xcc*,_|
		st := Pop(st);
		//||_,_,_,_,0x60*,0xcc*,_|
		//||_,_,_,_,0x60*,0xcc*,_|
		//||_,_,_,_,0x60*,0xcc*,_|
		st := Pop(st);
		//||_,_,_,0x60*,0xcc*,_|
		//||_,_,_,0x60*,0xcc*,_|
		//||_,_,_,0x60*,0xcc*,_|
		st := Pop(st);
		//||_,_,0x60*,0xcc*,_|
		st := Pop(st);
		//||_,0x60*,0xcc*,_|
		st := Pop(st);
		//||0x60*,0xcc*,_|
		st := Dup(st,2);
		//||0xcc*,0x60*,_,_|
		assume st.IsJumpDest(0xcc);
		st := Jump(st);
		st := block_0_0x00cc(st);
		return st;
	}

}
