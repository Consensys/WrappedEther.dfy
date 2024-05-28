include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module symbol {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x02e2(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02e2
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
		st := Push2(st,0x02ed);
		//|fp=0x0060|0x2ed,_,_|
		assume {:axiom} st.IsJumpDest(0x2ed);
		st := JumpI(st);
		if st.PC() == 0x2ed { st := block_0_0x02ed(st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x02ed(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02ed
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x02f5);
		//|fp=0x0060|0x2f5,_|
		st := Push2(st,0x0b30);
		//|fp=0x0060|0xb30,0x2f5,_|
		assume {:axiom} st.IsJumpDest(0xb30);
		st := Jump(st);
		st := block_0_0x0b30(st);
		return st;
	}

	method block_0_0x02f5(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02f5
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == 0x60)
	{
		var st := st';
		//||0x60,0x2f5,_|
		st := JumpDest(st);
		//||0x60,0x2f5,_|
		st := Push1(st,0x40);
		//||0x40,0x60,0x2f5,_|
		st := MLoad(st);
		//||_,0x60,0x2f5,_|
		st := Dup(st,1);
		//||_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		//||_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		//||0x20,_,_,_,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		//||_,_,_,0x60,0x2f5,_|
		st := Dup(st,3);
		st := block_0_0x02ff(st);
		return st;
	}

	method block_0_0x02ff(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02ff
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(4) == 0x60)
	{
		var st := st';
		//||_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		//||_,_,_,_,_,0x60,0x2f5,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := Sub(st);
		//||_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,3);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := MStore(st);
		//||_,_,_,0x60,0x2f5,_|
		st := Dup(st,4);
		//||0x60,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		//||_,0x60,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		//||0x60,_,0x60,_,_,_,0x60,0x2f5,_|
		st := MLoad(st);
		st := block_0_0x0307(st);
		return st;
	}

	method block_0_0x0307(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0307
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x60)
	{
		var st := st';
		//||_,_,0x60,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		//||_,_,_,0x60,_,_,_,0x60,0x2f5,_|
		st := MStore(st);
		//||_,0x60,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		//||0x20,_,0x60,_,_,_,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,_,0x60,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		//||_,0x60,_,_,_,0x60,0x2f5,_|
		st := Swap(st,2);
		//||_,0x60,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		//||0x60,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		//||0x60,0x60,_,_,_,0x60,0x2f5,_|
		st := MLoad(st);
		st := block_0_0x0310(st);
		return st;
	}

	method block_0_0x0310(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0310
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(1) == 0x60)
	{
		var st := st';
		//||_,0x60,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		//||0x60,_,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		//||0x20,0x60,_,_,_,_,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,0x60,_,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		//||0x80,_,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		//||_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		//||_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,4);
		//||_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,4);
		//||0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x00);
		st := block_0_0x031a(st);
		return st;
	}

	method block_0_0x031a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x031a
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires (st'.Peek(1) == 0x80)
	{
		var st := st';
		//||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := JumpDest(st);
		//||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,4);
		//||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		//||0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Lt(st);
		//||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := IsZero(st);
		//||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Push2(st,0x0335);
		//||0x335,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||0x335,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		assume {:axiom} st.IsJumpDest(0x335);
		st := JumpI(st);
		if st.PC() == 0x335 { st := block_0_0x0335(st); return st;}
		//||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		st := block_0_0x0324(st);
		return st;
	}

	method block_0_0x0324(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0324
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires (st'.Peek(2) == 0x80)
	{
		var st := st';
		//||0x00,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,3);
		//||0x80,0x00,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||0x80,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x80,0x00,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||0x80,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		//||0x80,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := MLoad(st);
		//||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		//||0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,5);
		//||_,0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_,0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		//||_,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := MStore(st);
		//||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		st := block_0_0x032d(st);
		return st;
	}

	method block_0_0x032d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x032d
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(2) == 0x80)
	{
		var st := st';
		//||0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||0x20,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		//||0x00,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,0x20,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// Havoc 0
		//||_,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,0x20,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,0x20,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		//||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// Havoc 0
		//||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		//||0x00,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		//||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Push2(st,0x031a);
		//||0x31a,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		assume {:axiom} st.IsJumpDest(0x31a);
		st := Jump(st);
		st := block_0_0x031a(st);
		return st;
	}

	method block_0_0x0335(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0335
	// Stack height(s)
	requires st'.Operands() == 12
	{
		var st := st';
		//||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := JumpDest(st);
		//||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		//||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		//||0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		//||_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		//||_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		//||_,0x80,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		//||0x80,_,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		//||_,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		st := block_0_0x033d(st);
		return st;
	}

	method block_0_0x033d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x033d
	// Stack height(s)
	requires st'.Operands() == 7
	{
		var st := st';
		//||_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		//||_,_,_,_,_,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		//||_,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		//||_,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x1f);
		//||0x1f,_,_,_,_,0x60,0x2f5,_|
		st := AndU5(st);
		//||_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := IsZero(st);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := Push2(st,0x0362);
		st := block_0_0x0348(st);
		return st;
	}

	method block_0_0x0348(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0348
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(0) == 0x362)
	{
		var st := st';
		//||0x362,_,_,_,_,_,0x60,0x2f5,_|
		assume {:axiom} st.IsJumpDest(0x362);
		st := JumpI(st);
		if st.PC() == 0x362 { st := block_0_0x0362(st); return st;}
		//||_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,3);
		//||_,_,_,_,_,_,0x60,0x2f5,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,_,_,_,_,_,0x60,0x2f5,_|
		st := Sub(st);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		//||_,_,_,_,_,_,0x60,0x2f5,_|
		st := MLoad(st);
		//||_,_,_,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x01);
		//||0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,4);
		st := block_0_0x0351(st);
		return st;
	}

	method block_0_0x0351(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0351
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(1) == 0x1)
	{
		var st := st';
		//||_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		//||0x20,_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		assert st.Peek(1) <= st.Peek(0);
		//||0x20,_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Sub(st);
		//||_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Push2(st,0x0100);
		//||0x100,_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Exp(st);
		//||_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Sub(st);
		//||_,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Not(st);
		//||_,_,_,_,_,_,_,0x60,0x2f5,_|
		st := And(st);
		//||_,_,_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		st := block_0_0x035c(st);
		return st;
	}

	method block_0_0x035c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x035c
	// Stack height(s)
	requires st'.Operands() == 10
	{
		var st := st';
		//||_,_,_,_,_,_,_,0x60,0x2f5,_|
		st := MStore(st);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		//||0x20,_,_,_,_,_,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,_,_,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := Swap(st,2);
		//||_,_,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		st := block_0_0x0362(st);
		return st;
	}

	method block_0_0x0362(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0362
	// Stack height(s)
	requires st'.Operands() == 7
	{
		var st := st';
		//||_,_,_,_,0x60,0x2f5,_|
		st := JumpDest(st);
		//||_,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		//||_,_,_,0x60,0x2f5,_|
		st := Swap(st,3);
		//||0x60,_,_,_,0x2f5,_|
		st := Pop(st);
		//||_,_,_,0x2f5,_|
		st := Pop(st);
		//||_,_,0x2f5,_|
		st := Pop(st);
		//||_,0x2f5,_|
		st := Push1(st,0x40);
		//||0x40,_,0x2f5,_|
		st := MLoad(st);
		st := block_0_0x036b(st);
		return st;
	}

	method block_0_0x036b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x036b
	// Stack height(s)
	requires st'.Operands() == 4
	{
		var st := st';
		//||_,_,0x2f5,_|
		st := Dup(st,1);
		//||_,_,_,0x2f5,_|
		st := Swap(st,2);
		//||_,_,_,0x2f5,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,_,_,0x2f5,_|
		st := Sub(st);
		//||_,_,0x2f5,_|
		st := Swap(st,1);
		//||_,_,0x2f5,_|
		st := Return(st);
		return st;
	}

	method block_0_0x0b30(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b30
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0x2f5)
	{
		var st := st';
		//|fp=0x0060|0x2f5,_|
		st := JumpDest(st);
		//|fp=0x0060|0x2f5,_|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,0x2f5,_|
		st := Dup(st,1);
		//|fp=0x0060|0x01,0x01,0x2f5,_|
		st := SLoad(st);
		//|fp=0x0060|_,0x01,0x2f5,_|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,_,0x01,0x2f5,_|
		st := Dup(st,2);
		//|fp=0x0060|_,0x01,_,0x01,0x2f5,_|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,_,0x01,_,0x01,0x2f5,_|
		st := AndU1(st);
		st := block_0_0x0b3b(st);
		return st;
	}

	method block_0_0x0b3b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b3b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(1) == 0x1 && st'.Peek(3) == 0x1 && st'.Peek(4) == 0x2f5)
	{
		var st := st';
		//|fp=0x0060|_,0x01,_,0x01,0x2f5,_|
		st := IsZero(st);
		//|fp=0x0060|_,0x01,_,0x01,0x2f5,_|
		st := Push2(st,0x0100);
		//|fp=0x0060|0x100,_,0x01,_,0x01,0x2f5,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x100,_,0x01,_,0x01,0x2f5,_|
		st := Mul(st);
		//|fp=0x0060|_,0x01,_,0x01,0x2f5,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|_,0x01,_,0x01,0x2f5,_|
		st := Sub(st);
		//|fp=0x0060|_,_,0x01,0x2f5,_|
		st := And(st);
		//|fp=0x0060|_,0x01,0x2f5,_|
		st := Push1(st,0x02);
		//|fp=0x0060|0x02,_,0x01,0x2f5,_|
		st := Swap(st,1);
		//|fp=0x0060|_,0x02,0x01,0x2f5,_|
		st := Div(st);
		st := block_0_0x0b46(st);
		return st;
	}

	method block_0_0x0b46(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b46
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(1) == 0x1 && st'.Peek(2) == 0x2f5)
	{
		var st := st';
		//|fp=0x0060|_,0x01,0x2f5,_|
		st := Dup(st,1);
		//|fp=0x0060|_,_,0x01,0x2f5,_|
		st := Push1(st,0x1f);
		//|fp=0x0060|0x1f,_,_,0x01,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x1f,_,_,0x01,0x2f5,_|
		st := Add(st);
		//|fp=0x0060|_,_,0x01,0x2f5,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,_,_,0x01,0x2f5,_|
		st := Dup(st,1);
		//|fp=0x0060|0x20,0x20,_,_,0x01,0x2f5,_|
		st := Swap(st,2);
		//|fp=0x0060|_,0x20,0x20,_,0x01,0x2f5,_|
		st := Div(st);
		//|fp=0x0060|_,0x20,_,0x01,0x2f5,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|_,0x20,_,0x01,0x2f5,_|
		st := Mul(st);
		st := block_0_0x0b50(st);
		return st;
	}

	method block_0_0x0b50(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b50
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(2) == 0x1 && st'.Peek(3) == 0x2f5)
	{
		var st := st';
		//|fp=0x0060|_,_,0x01,0x2f5,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,_,_,0x01,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,_,_,0x01,0x2f5,_|
		st := Add(st);
		//|fp=0x0060|_,_,0x01,0x2f5,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,_,_,0x01,0x2f5,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,_,_,0x01,0x2f5,_|
		st := Swap(st,1);
		//|fp=0x0060|_,0x60,_,0x01,0x2f5,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,_,0x60,_,0x01,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x60,_,0x60,_,0x01,0x2f5,_|
		st := Add(st);
		//|fp=0x0060|_,0x60,_,0x01,0x2f5,_|
		st := Push1(st,0x40);
		st := block_0_0x0b5b(st);
		return st;
	}

	method block_0_0x0b5b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b5b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(0) == 0x40 && st'.Peek(2) == 0x60 && st'.Peek(4) == 0x1 && st'.Peek(5) == 0x2f5)
	{
		var st := st';
		//|fp=0x0060|0x40,_,0x60,_,0x01,0x2f5,_|
		st := MStore(st);
		//||0x60,_,0x01,0x2f5,_|
		st := Dup(st,1);
		//||0x60,0x60,_,0x01,0x2f5,_|
		st := Swap(st,3);
		//||0x01,0x60,_,0x60,0x2f5,_|
		st := Swap(st,2);
		//||_,0x60,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		//||0x60,_,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		//||_,0x60,_,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		//||0x60,_,0x60,_,0x01,0x60,0x2f5,_|
		st := MStore(st);
		st := block_0_0x0b63(st);
		return st;
	}

	method block_0_0x0b63(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b63
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(2) == 0x1 && st'.Peek(3) == 0x60 && st'.Peek(4) == 0x2f5)
	{
		var st := st';
		//||0x60,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x20);
		//||0x20,0x60,_,0x01,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,0x60,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		//||0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,3);
		//||0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		//||0x01,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := SLoad(st);
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x01);
		//||0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		//||_,0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x01);
		st := block_0_0x0b6e(st);
		return st;
	}

	method block_0_0x0b6e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b6e
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(0) == 0x1 && st'.Peek(2) == 0x1 && st'.Peek(4) == 0x1 && st'.Peek(5) == 0x80 && st'.Peek(8) == 0x60 && st'.Peek(9) == 0x2f5)
	{
		var st := st';
		//||0x01,_,0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := AndU1(st);
		//||_,0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := IsZero(st);
		//||_,0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0100);
		//||0x100,_,0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		//||0x100,_,0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Mul(st);
		//||_,0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Sub(st);
		//||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := And(st);
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x02);
		//||0x02,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		st := block_0_0x0b79(st);
		return st;
	}

	method block_0_0x0b79(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b79
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(1) == 0x2 && st'.Peek(2) == 0x1 && st'.Peek(3) == 0x80 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
	{
		var st := st';
		//||_,0x02,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Div(st);
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		//||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := IsZero(st);
		//||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0bc6);
		//||0xbc6,_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		assume {:axiom} st.IsJumpDest(0xbc6);
		st := JumpI(st);
		if st.PC() == 0xbc6 { st := block_0_0x0bc6(st); return st;}
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		//||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x1f);
		//||0x1f,_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Lt(st);
		st := block_0_0x0b84(st);
		return st;
	}

	method block_0_0x0b84(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b84
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x1 && st'.Peek(3) == 0x80 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
	{
		var st := st';
		//||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0b9b);
		//||0xb9b,_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		assume {:axiom} st.IsJumpDest(0xb9b);
		st := JumpI(st);
		if st.PC() == 0xb9b { st := block_0_0x0b9b(st); return st;}
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0100);
		//||0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		//||0x100,0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,4);
		//||0x01,0x100,0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := SLoad(st);
		//||_,0x100,0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Div(st);
		//||_,0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		//||_,0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Mul(st);
		st := block_0_0x0b90(st);
		return st;
	}

	method block_0_0x0b90(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b90
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(3) == 0x80 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
	{
		var st := st';
		//||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,4);
		//||0x80,_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := MStore(st);
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Swap(st,2);
		//||0x80,0x01,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x20);
		//||0x20,0x80,0x01,_,_,0x01,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,0x80,0x01,_,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		//||0xa0,0x01,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,2);
		//||_,0x01,0xa0,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0bc6);
		//||0xbc6,_,0x01,0xa0,_,0x01,0x60,0x2f5,_|
		assume {:axiom} st.IsJumpDest(0xbc6);
		st := Jump(st);
		st := block_0_0x0bc6(st);
		return st;
	}

	method block_0_0x0b9b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b9b
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(2) == 0x80 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
	{
		var st := st';
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := JumpDest(st);
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,3);
		//||0x80,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x80,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Swap(st,2);
		//||0x80,0x01,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		//||0x01,0x80,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x00);
		//||0x00,0x01,0x80,_,_,0x01,0x60,0x2f5,_|
		st := MStore(st);
		//||0x80,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x20);
		st := block_0_0x0ba5(st);
		return st;
	}

	method block_0_0x0ba5(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ba5
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x80 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
	{
		var st := st';
		//||0x20,0x80,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x00);
		//||0x00,0x20,0x80,_,_,0x01,0x60,0x2f5,_|
		st := Keccak256(st);
		//||_,0x80,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		st := block_0_0x0ba9(st);
		return st;
	}

	method block_0_0x0ba9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ba9
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
	{
		var st := st';
		//||0x80,_,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := JumpDest(st);
		//||0x80,_,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		//||_,0x80,_,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := SLoad(st);
		//||_,0x80,_,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		//||0x80,_,0x80,_,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := MStore(st);
		//||0x80,_,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		//||_,0x80,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x01);
		//||0x01,_,0x80,_,_,0x01,0x60,0x2f5,_|
		//||0x01,_,_,_,_,0x01,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x01,_,0x80,_,_,0x01,0x60,0x2f5,_|
		//||0x01,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		st := block_0_0x0bb2(st);
		return st;
	}

	method block_0_0x0bb2(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bb2
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
	{
		var st := st';
		//||_,0x80,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		// Havoc 0
		//||_,0x80,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		//||0x80,_,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x20);
		//||0x20,0x80,_,_,_,0x01,0x60,0x2f5,_|
		//||0x20,_,_,_,_,0x01,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,0x80,_,_,_,0x01,0x60,0x2f5,_|
		//||0x20,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		//||0xa0,_,_,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		// Havoc 0
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		//||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,4);
		//||_,_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Gt(st);
		st := block_0_0x0bb9(st);
		return st;
	}

	method block_0_0x0bb9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bb9
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
	{
		var st := st';
		//||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0ba9);
		//||0xba9,_,_,_,_,_,0x01,0x60,0x2f5,_|
		assume {:axiom} st.IsJumpDest(0xba9);
		st := JumpI(st);
		if st.PC() == 0xba9 { st := block_0_0x0ba9(st); return st;}
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,3);
		//||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		//||_,_,_,_,_,0x01,0x60,0x2f5,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Sub(st);
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x1f);
		//||0x1f,_,_,_,_,0x01,0x60,0x2f5,_|
		st := AndU5(st);
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,3);
		st := block_0_0x0bc4(st);
		return st;
	}

	method block_0_0x0bc4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bc4
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
	{
		var st := st';
		//||_,_,_,_,_,0x01,0x60,0x2f5,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,2);
		st := block_0_0x0bc6(st);
		return st;
	}

	method block_0_0x0bc6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bc6
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
	{
		var st := st';
		//||_,0x01,0xa0,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := JumpDest(st);
		//||_,0x01,0xa0,_,0x01,0x60,0x2f5,_|
		//||_,_,_,_,0x01,0x60,0x2f5,_|
		//||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Pop(st);
		//||0x01,0xa0,_,0x01,0x60,0x2f5,_|
		//||_,_,_,0x01,0x60,0x2f5,_|
		//||0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Pop(st);
		//||0xa0,_,0x01,0x60,0x2f5,_|
		//||_,_,0x01,0x60,0x2f5,_|
		//||0x80,_,0x01,0x60,0x2f5,_|
		st := Pop(st);
		//||_,0x01,0x60,0x2f5,_|
		st := Pop(st);
		//||0x01,0x60,0x2f5,_|
		st := Pop(st);
		//||0x60,0x2f5,_|
		st := Dup(st,2);
		//||0x2f5,0x60,0x2f5,_|
		assume {:axiom} st.IsJumpDest(0x2f5);
		st := Jump(st);
		st := block_0_0x02f5(st);
		return st;
	}

}
