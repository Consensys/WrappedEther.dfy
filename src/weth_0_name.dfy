include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/libs/DafnyCrypto/src/dafny/util/math.dfy"
include "weth_0_header.dfy"

module name {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header
	import MathUtils

	method block_0_0x00b9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00b9
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	// Storate Items
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|name|
		st := JumpDest(st);
		//|fp=0x0060|name|
		st := CallValue(st);
		//|fp=0x0060|callVal,name|
		st := IsZero(st);
		//|fp=0x0060|callVal==0,name|
		st := Push2(st,0x00c4);
		//|fp=0x0060|0x2ed,callVal==0,name|
		assume {:axiom} st.IsJumpDest(0xc4);
		st := JumpI(st);
		if st.PC() == 0xc4 { 
			// call value is zero
			st := block_0_0x00c4(st); 
			return st;
		} 
		//|fp=0x0060|name|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,name|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,name|
		st := Revert(st); // revert if call value not zero
		return st;
	}

	method block_0_0x00c4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00c4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	// Storate Items
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|name|
		st := JumpDest(st);
		//|fp=0x0060|name|
		st := Push2(st,0x00cc);
		//|fp=0x0060|0xcc,name|
		st := Push2(st,0x04dd);
		//|fp=0x0060|0x4dd,0xcc,name|
		assume {:axiom} st.IsJumpDest(0x4dd);
		st := Jump(st);
		//|fp=0x0060|0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x04dd(st);
		return st;
	}

	method block_0_0x00cc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00cc
	// Free memory pointer
	requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires st'.evm.stack.contents == [0x60,0xcc,st'.Peek(2)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0x60,0xcc,name|
		st := JumpDest(st);
		//||0x60,0xcc,name|
		st := Push1(st,0x40);
		//||0x40,0x60,0xcc,name|
		st := MLoad(st);
		//||st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,1);
		//||st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,1);
		//||st.Read(0x40),st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Push1(st,0x20);
		//||0x20,st.Read(0x40),st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,3);
		//||st.Read(0x40),0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x00d6(st);
		return st;
	}

	method block_0_0x00d6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00d6
	// Stack height(s)
	requires st'.Operands() == 7
	// Free memory pointer
	requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Static stack items
	requires st'.evm.stack.contents == [0xa0,0xc0,0xa0,0xa0,0x60,0xcc,st'.Peek(6)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||st.Read(0x40),0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||0xc0,st.Read(0x40),0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//||0x20,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,3);
		//||st.Read(0x40),0x20,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x00d9(st);
		return st;
	}

	method block_0_0x00d9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00d9
	// Free memory pointer
	requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0xa0,0x20,0xc0,0xa0,0xa0,0x60,0xcc,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);
		//||0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name| i.e. st.Read(st.Read(0x40))==0x20
		stackLemma(st,st.Operands());
		st := block_0_0x00da(st);
		return st;
	}

	method block_0_0x00da(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00da
	// Free memory pointer
	requires st'.MemSize() >= 0xc0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires st'.evm.stack.contents == [0xc0,0xa0,0xa0,0x60,0xcc,st'.Peek(5)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Dup(st,4);
		//||0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||0xc0,0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||0x60,0xc0,0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := MLoad(st);
		//||st.Read(0x60),0xc0,0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x00de(st);
		return st;
	}

	method block_0_0x00de(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00de
	// Free memory pointer
	requires st'.MemSize() >= 0xc0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [st'.Read(0x60),0xc0,0x60,0xc0,0xa0,0xa0,0x60,0xcc,st'.Peek(8)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||st.Read(0x60),0xc0,0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||0xc0,st.Read(0x60),0xc0,0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := MStore(st);
		//||0xc0,0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name| i.e. st.Read(0xc0)==st.Read(0x60)
		st := Push1(st,0x20);
		//||0x20,0xc0,0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		stackLemma(st,st.Operands());
		st := block_0_0x00e2(st);
		return st;
	}

	method block_0_0x00e2(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00e2
	// Stack height(s)
	requires st'.Operands() == 9
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Static stack items
	requires st'.evm.stack.contents == [0x20,0xc0,0x60,0xc0,0xa0,0xa0,0x60,0xcc,st'.Peek(8)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0x20,0xc0,0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||0xe0,0x60,0xc0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Swap(st,2);
		//||0xc0,0x60,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Pop(st);
		//||0x60,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Dup(st,1);
		//||0x60,0x60,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := MLoad(st);
		//||st.Read(0x60),0x60,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		stackLemma(st,st.Operands());
		assert st.evm.stack.contents == [0x0d,0x60,0xe0,0xa0,0xa0,0x60,0xcc,st.Peek(7)];
		st := block_0_0x00e7(st);
		return st;
	}

	method block_0_0x00e7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00e7
	// Stack height(s)
	requires st'.Operands() == 8
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Static stack items
	requires st'.evm.stack.contents == [0x0d,0x60,0xe0,0xa0,0xa0,0x60,0xcc,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||st.Read(0x60),0x60,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Swap(st,1);
		//||0x60,st.Read(0x60),0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Push1(st,0x20);
		//||0x20,0x60,st.Read(0x60),0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||0x80,st.Read(0x60),0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Swap(st,1);
		//||st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,1);
		//||st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,4);
		//||0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,4);
		//||0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Push1(st,0x00);
		//||0x00,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x00f1(0,st);
		return st;
	}

	method block_0_0x00f1(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00f1
	// Stack height(s)
	requires st'.Operands() == 12
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	requires i > 0 ==>  st'.MemSize() >= 0x100 && st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Static stack items
	requires st'.Peek(0) as nat == i as nat * 0x20 <= 0x0d as nat + 0x1f
	requires st'.evm.stack.contents == [st'.Peek(0),0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,st'.Peek(11)]
	// Termination
	decreases (st'.Read(0x60)+0x1f) - i*0x20,2
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||i*0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := JumpDest(st);
		//||i*0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,4);
		//||st.Read(0x60),i*0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||i*0x20,st.Read(0x60),i*0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Lt(st); // y < x
		//||i*0x20<st.Read(0x60),i*0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := IsZero(st);
		//||i*0x20>=st.Read(0x60),i*0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Push2(st,0x010c);
		//||0x10c,i*0x20>=st.Read(0x60),i*0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0x10c);
		st := JumpI(st);
		if st.PC() == 0x10c { 
			//assert i == 1;
			//||i*0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
			stackLemma(st,st.Operands());
			st := block_0_0x010c(st); 
			return st;
		
		} // ie. first iteration, i == 0 (i.e. 0 < 0x0d)
		// ||0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		st := Dup(st,1);
		// ||0x00,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x00fb(i,st); 
		return st;
	}

	method block_0_0x00fb(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00fb
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires st'.evm.stack.contents == [0,0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,st'.Peek(12)]
	// Termination
	requires i == 0
	decreases  0x0d - i,4
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |i,i,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,name|
		st := Dup(st,3);
		// ||0x80,i,i,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0x80+i,i,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,name|
		stackLemma(st,st.Operands());
		st := block_0_0x00fd(i,st);
		return st;
	}

	method block_0_0x00fd(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00fd
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires st'.evm.stack.contents == [0x80,0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,st'.Peek(12)]
	// Termination
	requires i==0
	decreases  0x0d - i,3
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0x80,0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		st := MLoad(st);
		// ||st.Read(0x80),0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,2);
		// ||0x00,st.Read(0x80),0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,5);
		// ||0xe0,0x00,st.Read(0x80),0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0xe0,st.Read(0x80),0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0101(i,st);
		return st;
	}

	method block_0_0x0101(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0101
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 14
	// Static stack items
	requires i == 0
	requires st'.evm.stack.contents == [0xe0,st'.Read(0x80),0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,st'.Peek(13)]
	// Termination
	decreases  0x0d - i,2
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0xe0,st.Read(0x80),0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		st := MStore(st);
		// ||0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0104(i,st);
		return st;
	}

	method block_0_0x0104(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0102
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	requires st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
		// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires i == 0
	requires st'.evm.stack.contents == [0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,st'.Peek(11)]
	// Termination
	decreases  0x0d - i,1
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		st := Push1(st,0x20);
		// ||0x20,0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,2);
		// ||0x00,0x20,0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||0x20,0x0,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		st := Swap(st,1);
		//||0x0,0x20,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		st := Pop(st);
		//||0x20,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		assert st.Peek(0) == 0x20; /// NB: this additional assert was needed and the position determines whether the block verifies or not
		st := Push2(st,0x00f1);
		// ||0xf1,0x20,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0xf1);
		st := Jump(st);
		// ||0x20,0x80,0xe0,0x0d,0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x00f1(i+1,st);
		return st;
	}

	method block_0_0x010c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x010c
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires st'.evm.stack.contents == [st'.Peek(0),st'.Peek(1),st'.Peek(2),st'.Peek(3),0x0d,0x80,0xe0,0xa0,0xa0,0x60,0xcc,st'.Peek(11)]
	
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := JumpDest(st);
		//||0x20,0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Pop(st);
		//||0x80,0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Pop(st);
		//||0xe0,st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Pop(st);
		//||st.Read(0x60),st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Pop(st);
		//||st.Read(0x60),0x80,0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Swap(st,1);
		//||0x80,st.Read(0x60),0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Pop(st);
		//||st.Read(0x60),0xe0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Swap(st,1);
		//||0xe0,st.Read(0x60),st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0114(st);
		return st;
	}

	method block_0_0x0114(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0114
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [0xe0,0x0d,0xa0,0xa0,0x60,0xcc,st'.Peek(6)]
	
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0xe0,0xd,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,2);
		//||0xd,0xe0,0xd,0xa0,0xa0,0x60,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||0xed,0xd,0xa0,0xa0,0x60,0xcc,name|
		st := Swap(st,1);
		//||0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := Push1(st,0x1f);
		//||0x1f,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := block_0_0x0119(st);
		return st;
	}

	method block_0_0x0119(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0119
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0x1f,0x0d,0xed,0xa0,0xa0,0x60,0xcc,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := AndU5(st);
		stackLemma(st,st.Operands());
		st := block_0_0x011a(st);
		return st;
	}

	method block_0_0x011a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x011a
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [0x0d,0xed,0xa0,0xa0,0x60,0xcc,st'.Peek(6)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,1);
		//||0x0d,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := IsZero(st);
		//||0x0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := Push2(st,0x0139);
		//||0x139,0x0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents == [0x139,0x0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,st.Peek(8)];
		st := block_0_0x011f(st);
		return st;
	}

	method block_0_0x011f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x011f
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x139,0x0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,st'.Peek(8)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0x139,0x0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0x139);
		st := JumpI(st);
		if st.PC() == 0x139 { 
			assert false; // Dead code i.e. (len % 32) == 0 and since whole words of output, no need for masking of last word of string output
			//||st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
			//stackLemma(st,st.Operands());
			//st := block_0_0x0139(st); 
			//return st;
		} 
		//||0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,1);
		//||0x0d,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,3);
		//||0xed,0x0d,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		assert st.Peek(1) <= st.Peek(0); 
		st := Sub(st);
		assert st.Peek(0) == 0xe0;
		//||0xe0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,1);
		//||0xe0,0xe0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := MLoad(st);
		//||st.Read(0xe0),0xe0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := Push1(st,0x01);
		//||0x01,st.Read(0xe0),0xe0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,4);
		// //||0x0d,0x01,st.Read(0xe0),0xe0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0128(st);
		return st;
	}

	method block_0_0x0128(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0128
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x0d,0x1,st'.Read(0xe0),0xe0,0x0d,0xed,0xa0,0xa0,0x60,0xcc,st'.Peek(10)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||len,0x1,st.Read(0xe0),0xe0,st.Peek(4),st.Peek(5),0xa0,0xa0,0x60,0xcc,name|
		st := Push1(st,0x20);
		//||0x20,len,0x1,st.Read(0xe0),0xe0,st.Peek(4),st.Peek(5),0xa0,0xa0,0x60,0xcc,name|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//assert st.evm.stack.contents == [0x13,0x1,st.Read(0xe0),0xe0,st.Peek(4),st.Peek(5),0xa0,0xa0,0x60,0xcc,st.Peek(10)];
		
		//||0x13,0x1,st.Read(0xe0),0xe0,st.Peek(4),st.Peek(5),0xa0,0xa0,0x60,0xcc,name|
		st := Push2(st,0x0100);
		//||0x0100,0x13,0x1,st.Read(0xe0),0xe0,st.Peek(4),st.Peek(5),0xa0,0xa0,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x012e(st);
		return st;
	}

	method block_0_0x012e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x012e
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires st'.evm.stack.contents == [0x100,0x13,0x1,st'.Read(0xe0),0xe0,st'.Peek(5),st'.Peek(6),0xa0,0xa0,0x60,0xcc,st'.Peek(11)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0x0100,0x13,0x1,st.Read(0xe0),0xe0,st.Peek(4),st.Peek(5),0xa0,0xa0,0x60,0xcc,name|
		st := Exp(st);
		//||0x100000000000000000000000000000000000000,0x1,st.Read(0xe0),0xe0,st.Peek(4),st.Peek(5),0xa0,0xa0,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x012f(st);
		return st;
	}

	method block_0_0x012f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x012f
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x100000000000000000000000000000000000000,0x1,st'.Read(0xe0),0xe0,st'.Peek(4),st'.Peek(5),0xa0,0xa0,0x60,0xcc,st'.Peek(10)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		assert st.Peek(1) <= st.Peek(0);
		var temp := st.Peek(0) - st.Peek(1); 
		//||0x100000000000000000000000000000000000000,0x1,st.Read(0xe0),0xe0,st.Peek(4),st.Peek(5),0xa0,0xa0,0x60,0xcc,name|
		st := Sub(st);
		//||0xffffffffffffffffffffffffffffffffffffff,st.Read(0xe0),0xe0,st.Peek(3),st.Peek(4),0xa0,0xa0,0x60,0xcc,name|
		assert st.Peek(0) == temp;
		//assert st.Peek(0) == 0x100000000000000000000000000000000000000 - 0x1 == 0xffffffffffffffffffffffffffffffffffffff;
		st := Not(st);
		//||0xffffffffffffffffffffffffff00000000000000000000000000000000000000,st.Read(0xe0),0xe0,st.Peek(3),st.Peek(4),0xa0,0xa0,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0131(st);
		return st;
	}

	method block_0_0x0131(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0131
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires st'.evm.stack.contents == [0xffffffffffffffffffffffffff00000000000000000000000000000000000000,st'.Read(0xe0),0xe0,st'.Peek(3),st'.Peek(4),0xa0,0xa0,0x60,0xcc,st'.Peek(9)]
	
	{
		var st := st';
		stackLemma(st,st.Operands());
		assert st.Peek(1) % 0x100000000000000000000000000000000000000 == 0;
		st := AndUpper13Bytes(st);
		//||st.Read(0xe0),0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		st := Dup(st,2);
		//||0xe0,st.Read(0xe0),0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0133(st);
		return st;
	}

	method block_0_0x0133(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0133
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires st'.evm.stack.contents == [0xe0,st'.Read(0xe0),0xe0,st'.Peek(3),st'.Peek(4),0xa0,0xa0,0x60,0xcc,st'.Peek(9)]
	
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0xe0,st.Read(0xe0),0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		st := MStore(st);
		//||0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		st := block_0_0x0134(st);
		return st;
	}

	method block_0_0x0134(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0134
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0xe0,st'.Peek(1),st'.Peek(2),0xa0,0xa0,0x60,0xcc,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		st := Push1(st,0x20);
		//||0x20,0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||0x100,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		st := Swap(st,2);
		//||0xed,len%32,0x100,0xa0,0xa0,*ptr(len),0xcc,name|
		st := Pop(st);
		//||len%32,0x100,0xa0,0xa0,*ptr(len),0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0139(st);
		return st;
	}

	method block_0_0x0139(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0139
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [st'.Peek(0),0x100,0xa0,0xa0,0x60,0xcc,st'.Peek(6)]
	
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||len%32,0x100,0xa0,0xa0,*ptr(len),0xcc,name|
		st := JumpDest(st);
		//||st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Pop(st);
		//||st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Swap(st,3);
		//||0x60,st.Read(0x40),st.Read(0x40),st.Read(0x40)+0x40,0xcc,name|
		st := Pop(st);
		//||st.Read(0x40),st.Read(0x40),st.Read(0x40)+0x40,0xcc,name|
		st := Pop(st);
		//||st.Read(0x40),st.Read(0x40)+0x40,0xcc,name|
		st := Pop(st);
		//||st.Read(0x40)+0x40,0xcc,name|
		st := Push1(st,0x40);
		//||0x40,st.Read(0x40)+0x40,0xcc,name|
		st := MLoad(st);
		//||st.Read(0x40),st.Read(0x40)+0x40,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0142(st);
		return st;
	}

	method block_0_0x0142(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0142
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									//&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == 0x5772617070656420457468657200000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires st'.evm.stack.contents == [0xa0,0x100,0xcc,st'.Peek(3)]
	
	// ensures data := Memory.Slice(st.evm.memory, 0xa0, 0x60);
	// 0000000000000000000000000000000000000000000000000000000000000020 i.e. array starts at pos 32 (the 2nd word)
	// 000000000000000000000000000000000000000000000000000000000000000d i.e. array size of 13 bytes
	// 0x5772617070656420457468657200000000000000000000000000000000000000 i.e. string == "Wrapped Ether"
	
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||st.Read(0x40),st.Read(0x40)+0x40,0xcc,name|
		st := Dup(st,1);
		//||st.Read(0x40),st.Read(0x40),st.Read(0x40)+0x40,0xcc,name|
		st := Swap(st,2);
		//||st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0xcc,name|
		assert st.Peek(1) <= st.Peek(0); 
		st := Sub(st);
		//||0x40,st.Read(0x40),0xcc,name|
		st := Swap(st,1);
		//||st.Read(0x40),0x40,0xcc,name|
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
	requires st'.evm.stack.contents == [0xcc,st'.Peek(1)]
	// Storate Items
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xcc,name|
		st := JumpDest(st);
		//|fp=0x0060|0xcc,name|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0xcc,name|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,0xcc,name|
		st := SLoad(st);
		//|fp=0x0060|st.Load(0)=len*2,0x00,0xcc,name|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,len*2,0x00,0xcc,name|
		st := Dup(st,2);
		//|fp=0x0060|len*2,0x01,len*2,0x00,0xcc,name|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,len*2,0x01,len*2,0x00,0xcc,name|
		st := AndU1(st);
		//|fp=0x0060|0,0x01,len*2,0x00,0xcc,name|
		stackLemma(st,st.Operands());
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
	requires st'.evm.stack.contents == [0x0,0x01,st'.Load(0x0),0x0,0xcc,st'.Peek(5)]

  	// Storate Items
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0,0x01,len*2,0x00,0xcc,name|
		st := IsZero(st);
		//|fp=0x0060|1,0x01,len*2,0x00,0xcc,name|
		st := Push2(st,0x0100);
		//|fp=0x0060|0x100,1,0x01,len*2,0x00,0xcc,name|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		//|fp=0x0060|0x100,0x01,len*2,0x00,0xcc,name|
		assert st.Peek(1) <= st.Peek(0); 
		st := Sub(st);
		//|fp=0x0060|0xff,len*2,0x00,0xcc,name|
		//assert st.Peek(0) in {MAX_U256 as u256, 0xFF};
		// ==========================================================
		// NOTE: Reimplemented following to avoid need to reason about bitvector
		// arithmetic.
		// st := And(st);
		if st.Peek(0) == MAX_U256 as u256 { 
			// Masking against MAX_U256 (a nop)
			st := st.Pop().Next();
			assert st.Peek(0) == st.Load(0x0);
		} else {
			// Masking against 0xFF
			st := AndU8(st); // i.e. since short string get first byte of st.Load(0x01), i.e. len*2
			assert st.Peek(0) == st.Load(0x0)%256;
		}
		// ==========================================================
		// |fp=0x0060|len*2,0x00,0xcc,name|
		st := Push1(st,0x02);
		// |fp=0x0060|0x02,len*2,0x00,0xcc,name|
		st := Swap(st,1);
		// |fp=0x0060|len*2,0x02,0x00,0xcc,name|
		assert st.Peek(1) != 0;
		st := Div(st);
		// |fp=0x0060|len=0xd,0x00,0xcc,name|
		stackLemma(st,st.Operands());
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
	requires st'.evm.stack.contents == [0x0d,0x0,0xcc,st'.Peek(3)]

	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |fp=0x0060|len=0xd,0x00,0xcc,name|
		st := Dup(st,1);
		// |fp=0x0060|len,len,0x00,0xcc,name|
		st := Push1(st,0x1f);
		// |fp=0x0060|0x1f,len,len,0x00,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |fp=0x0060|len+0x1f=0x2c,len,0x00,0xcc,name|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,len+0x1f,len,0x00,0xcc,name|
		st := Dup(st,1);
		// |fp=0x0060|0x20,0x20,len+0x1f,len,0x00,0xcc,name|
		st := Swap(st,2);
		// |fp=0x0060|len+0x1f,0x20,0x20,len,0x00,0xcc,name|
		assert st.Peek(1) != 0;
		st := Div(st);
		// |fp=0x0060|0x1,0x20,len,0x00,0xcc,name|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		// |fp=0x0060|0x20,len,0x00,0xcc,name| // n is len rounded up
		stackLemma(st,st.Operands());
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
	requires st'.evm.stack.contents == [0x20,0x0d,0x0,0xcc,st'.Peek(4)]

	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |fp=0x0060|0x20,len,0x00,0xcc,name|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,len,0x00,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |fp=0x0060|0x40,len,0x00,0xcc,name|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0x40,len,0x00,0xcc,name|
		st := MLoad(st);
		// |fp=0x0060|mp=Read(0x40),0x40,len,0x00,0xcc,name|
		st := Swap(st,1);
		// |fp=0x0060|0x40,mp=0x60,len,0x00,0xcc,name|
		st := Dup(st,2);
		// |fp=0x0060|mp,0x40,mp,len,0x00,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |fp=0x0060|mp+0x40,mp,len,0x00,0xcc,name|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0xa0,mp,len,0x00,0xcc,name|
		stackLemma(st,st.Operands());
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
	requires st'.evm.stack.contents == [0x40,0xa0,0x60,0x0d,0x0,0xcc,st'.Peek(6)]

	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |fp=0x0060|0x40,0xa0,mp,len,0x00,0xcc,name|
		st := MStore(st);
		// |fp=0x0060|prev_mp==0x60,len,0x00,0xcc,name| i.e. st.Read(0x40) == fmp+*+0x20, fmp' refers to previous fmp == 0x60
		st := Dup(st,1);
		// ||0x60,0x60,len,0x00,0xcc,name|
		st := Swap(st,3);
		// ||0x00,0x60,len,0x60,0xcc,name|
		st := Swap(st,2);
		// ||len,0x60,0x00,0x60,0xcc,name|
		st := Swap(st,1);
		// ||0x60,len,0x00,0x60,0xcc,name|
		st := Dup(st,2);
		// ||len,0x60,len,0x00,0x60,0xcc,name|
		st := Dup(st,2);
		// ||0x60,len,0x60,len,0x00,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x050f(st);
		return st;
	}

	method block_0_0x050f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x050f
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0xa0 
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0x60,0x0d,0x60,0x0d,0x0,0x60,0xcc,st'.Peek(7)]
  	
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);		
		// ||0x60,len,0x00,0x60,0xcc,name| i.e. st.Read(0x60) == len
		stackLemma(st,st.Operands());
		st := block_0_0x0510(st);
		return st;
	}

	method block_0_0x0510(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0510
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x0d // len
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires st'.evm.stack.contents == [0x60,0x0d,0x0,0x60,0xcc,st'.Peek(5)]
  	
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0x60,len,0x00,0x60,0xcc,name|
		st := Push1(st,0x20);
		// ||0x20,0x60,len,0x00,0x60,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0x80,len,0x00,0x60,0xcc,name|
		st := Dup(st,3);
		// ||0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Dup(st,1);
		// ||0x00,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := SLoad(st);
		// ||st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Push1(st,0x01);
		// ||0x01,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Dup(st,2);
		// ||st.Load(0),0x01,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Push1(st,0x01);
		// ||0x01,st.Load(0),0x01,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x051b(st);
		return st;
	}

	method block_0_0x051b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x051b
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x0d         
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x01,st'.Load(0x0),0x01,st'.Load(0x0),0x0,0x080,0x0d,0x0,0x60,0xcc,st'.Peek(10)]
  	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0x01,st.Load(0),0x01,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		st := AndU1(st);
		// ||st.Load(0)%2,0x01,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		st := IsZero(st);
		// ||(st.Load(0)%2)==0,0x01,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Push2(st,0x0100);
		// ||0x100,(st.Load(0)%2)==0,0x01,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		// ||{0,0x100},0x01,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		assert st.Peek(1) <= st.Peek(0); 
		st := Sub(st);
		//assert st.Peek(0) in {MAX_U256 as u256, 0xFF};
		// ||0xff,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		// ==========================================================
		// NOTE: Reimplemented following to avoid need to reason about bitvector
		// arithmetic.
		//st := And(st);
		if st.Peek(0) == MAX_U256 as u256 { 
			// Masking against MAX_U256 (a nop)
			st := st.Pop().Next();
		} else {
			// Masking against 0xFF
			st := AndU8(st);
			assert st.Peek(0) == 0x01a;
		}
		// ==========================================================
		// ||st.Load(0)*,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Push1(st,0x02);
		// ||0x02,st.Load(0)*,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Swap(st,1);
		// ||st.Load(0)*,0x02,0x00,0x80,len,0x00,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0526(st);
		return st;
	}

	method block_0_0x0526(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0526
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x0d     
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x1a,0x02,0x0,0x80,0x0d,0x0,0x60,0xcc,st'.Peek(8)]
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||len*2,0x02,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert st.Peek(1) != 0;
		st := Div(st);
		// ||len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Dup(st,1);
		// ||len,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := IsZero(st);
		// ||len==0,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Push2(st,0x0573);
		// ||0x573,len==0,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0x573);
		st := JumpI(st);
		if st.PC() == 0x573 { 
			assert false;
			// ||len,0x00,0x80,len,0x00,0x60,0xcc,name|
			stackLemma(st,st.Operands());
			st := block_0_0x0573(st); 
			return st;
		} 
		// ||len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Dup(st,1);
		// ||len,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Push1(st,0x1f);
		// ||0x1f,len,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Lt(st);
		// ||0x1f<len,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0531(st);
		return st;
	}

	method block_0_0x0531(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0531
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x0d      
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x0d,0x0,0x80,0x0d,0x0,0x60,0xcc,st'.Peek(8)]
	
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0x0,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Push2(st,0x0548);
		// ||0x548,0x0,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0x548);
		st := JumpI(st);
		if st.PC() == 0x548 { 
			// Deadcode begins here.  The reason is that the following code is used
			// to account for copying strings whose length exceeds 31 bytes.
			// However, the actual length of the string involved in this case
			// ("Wrapped Ether") is only 13 bytes.
			// i.e. this path would imply len > 0x1f
			assert false;
			//st := block_0_0x0548(st); return st;
		} 
		// ||len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert st.Peek(0) == 0x0d;
		st := Push2(st,0x0100);
		// ||0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
    	st := Dup(st,1);
		// ||0x100,0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Dup(st,4);
		// ||0x00,0x100,0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := SLoad(st);
    	// ||st.Load(0),0x100,0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert st.Peek(1) != 0;
		st := Div(st);
		// ||st.Load(0x1)>>8,0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		// ||(st.Load(0x1)>>8)>>8,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x053d(st);
		return st;
	}

	method block_0_0x053d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x053d
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x0d      
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x5772617070656420457468657200000000000000000000000000000000000000,0x0d,0x0,0x80,0x0d,0x0,0x60,0xcc,st'.Peek(8)]
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||(st.Load(0x0)>>8)<<8,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Dup(st,4);
		// ||0x80,(st.Load(0x0)>>8)<<8,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := MStore(st);
		// ||len,0x00,0x80,len,0x00,0x60,0xcc,name| st.Read(0x80) == 0
		st := Swap(st,2);
		// ||0x80,0x00,0xd,0xd,0x00,0x60,0xcc,name|
		st := Push1(st,0x20);
		// ||0x20,0x80,0x00,0xd,0xd,0x00,0x60,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0xa0,0x00,0xd,0xd,0x00,0x60,0xcc,name|
		st := Swap(st,2);
		// ||0xd,0x00,0xa0,0xd,0x00,0x60,0xcc,name|
		st := Push2(st,0x0573);
		// ||0x573,0xd,0x00,0xa0,0xd,0x00,0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0x573);
		st := Jump(st);
		// ||0xd,0x00,0xa0,0xd,0x00,0x60,0xcc,name|
		stackLemma(st,st.Operands());
		st := block_0_0x0573(st);
		return st;
	}

	// this path is impossible i.e len > 0x1f where as here len == 4
	// method block_0_0x0548(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0548
	// // Free Memory Pointer
	// requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	// requires (st'.Read(0x60) <= 0xffff)	
	// // Stack height(s)
	// requires st'.Operands() == 8
	// {
	// 	var st := st';
	// 	st := JumpDest(st);
	// 	st := Dup(st,3);
	// 	st := Add(st);
	// 	var n := st.Peek(0);
	// 	st := Swap(st,2);
	// 	st := Swap(st,1);
	// 	st := Push1(st,0x00);
	// 	st := MStore(st);
	// 	st := Push1(st,0x20);
	// 	st := block_0_0x0552(n,st);
	// 	return st;
	// }

	// method block_0_0x0552(n: u256,st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0552
	// // Free Memory Pointer
	// requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff && st'.Read(0x00) == 0x00
	// requires (st'.Read(0x60) <= 0xffff)	
	// // Stack height(s)
	// requires st'.Operands() == 8
	// {
	// 	var st := st';
	// 	st := Push1(st,0x00);
	// 	st := Keccak256(st); // sha3(st.Read(0x00))
	// 	st := Swap(st,1);
	// 	st := block_0_0x0556(0x80,n,st);
	// 	return st;
	// }

	// method block_0_0x0556(i: u256, n: u256,st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0556
	// // Free Memory Pointer
	// requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	// requires (st'.Read(0x60) <= 0xffff)	
	// // Stack height(s)
	// requires st'.Operands() == 8
	// {
	// 	var st := st';
	// 	st := JumpDest(st);
	// 	st := Dup(st,2);
	// 	st := SLoad(st);
	// 	st := Dup(st,2);
	// 	st := MStore(st);
	// 	st := Swap(st,1);
	// 	st := Push1(st,0x01);
	// 	st := Add(st);
	// 	st := block_0_0x055f(i,n,st);
	// 	return st;
	// }

	// method block_0_0x055f(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x055f
	// // Free memory pointer
	// requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	// requires (st'.Read(0x60) <= 0xffff)
	// // Stack height(s)
	// requires st'.Operands() == 8
	// {
	// 	var st := st';
	// 	st := Swap(st,1);
	// 	st := Push1(st,0x20);
	// 	st := Add(st);
	// 	st := Dup(st,1);
	// 	st := Dup(st,4);
	// 	st := Gt(st);
	// 	st := block_0_0x0566(i+0x20,n,st);
	// 	return st;
	// }

	// method block_0_0x0566(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0566
	// // Free memory pointer
	// requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	// requires (st'.Read(0x60) <= 0xffff)
	// // Stack height(s)
	// requires st'.Operands() == 9
	// {
	// 	var st := st';
	// 	st := Push2(st,0x0556);
	// 	assume {:axiom} st.IsJumpDest(0x556);
	// 	st := JumpI(st);
	// 	if st.PC() == 0x556 { 
	// 		st := block_0_0x0556(i,n,st); 
	// 		return st; 
	// 		}
	// 	//n <= i
	// 	st := Dup(st,3);
	// 	st := Swap(st,1);
	// 	assert st.Peek(1) <= st.Peek(0);
	// 	st := Sub(st);
	// 	st := Push1(st,0x1f);
	// 	st := AndU5(st);
	// 	st := Dup(st,3);
	// 	st := block_0_0x0571(st);
	// 	return st;
	// }

	// method block_0_0x0571(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0571
	// // Free memory pointer
	// requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	// requires (st'.Read(0x60) <= 0xffff)
	// // Stack height(s)
	// requires st'.Operands() == 9
	// {
	// 	var st := st';
	// 	assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
	// 	st := Add(st);
	// 	st := Swap(st,2);
	// 	st := block_0_0x0573(st);
	// 	return st;
	// }

	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	method block_0_0x0573(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0573
	// Free memory pointer
	requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [st'.Peek(0),st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0x60,0xcc,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||len,0x00,0xa0,len,0x00,*ptr(len),0xcc,name| 
		st := JumpDest(st);
		//||len,0x00,0xa0,len,0x00,*ptr(len),0xcc,name| 
		st := Pop(st);
		//||0x00,0xa0,len,0x00,*ptr(len),0xcc,name| 
		st := Pop(st);
		//||0xa0,len,0x00,*ptr(len),0xcc,name| 
		st := Pop(st);
		//||len,0x00,0x60,0xcc,name|
		st := Pop(st);
		// ||0x00,0x60,0xcc,name|
		st := Pop(st);
		//||0x60,0xcc,name|
		st := Dup(st,2);
		//||0xcc,0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0xcc);
		st := Jump(st);
		stackLemma(st,st.Operands());
		st := block_0_0x00cc(st);
		return st;
	}

}
