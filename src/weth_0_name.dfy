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
	requires (st'.Peek(0) == 0x60 && st'.Peek(1) == 0xcc)	
	{
		var st := st';
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
		//||st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,3);
		//||st.Read(0x40),st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
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
	requires (st'.Peek(0) == 0xa0 && st'.Peek(1) == 0xc0 && st'.Peek(2) == 0xa0 && st'.Peek(3) == 0xa0 && st'.Peek(4) == 0x60 && st'.Peek(5) == 0xcc)
	
	{
		var st := st';
		//||st.Read(0x40),st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//||0x20,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,3);
		//||st.Read(0x40),0x20,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := MStore(st);
		//||st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name| i.e. st.Read(st.Read(0x40))==0x20
		st := Dup(st,4);
		//||0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||st.Read(0x40)+0x20,0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||0x60,st.Read(0x40)+0x20,0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := MLoad(st);
		//||st.Read(0x60),st.Read(0x40)+0x20,0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
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
	requires (st'.Peek(0) == st'.Read(0x60) && st'.Peek(1) == 0xc0 && st'.Peek(2) == st'.Peek(6) == 0x60 && st'.Peek(3) == 0xc0  && st'.Peek(4) == st'.Peek(5) == 0xa0 && st'.Peek(7) == 0xcc)

	{
		var st := st';
		//||st.Read(0x60),st.Read(0x40)+0x20,0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||st.Read(0x40)+0x20,st.Read(0x60),st.Read(0x40)+0x20,0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := MStore(st);
		//||st.Read(0x40)+0x20,0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,name| i.e. st.Read(st.Read(0x40)+0x20)==st.Read(0x60)
		st := Push1(st,0x20);
		//||0x20,st.Read(0x40)+0x20,0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := block_0_0x00e2(st);
		return st;
	}

	method block_0_0x00e2(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00e2
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0xc0 && st'.Peek(2) == st'.Peek(6) == 0x60 && st'.Peek(3) == 0xc0 && st'.Peek(4) == st'.Peek(5) == 0xa0 && st'.Peek(7) == 0xcc)
  	
	{
		var st := st';
		//||0x20,st.Read(0x40)+0x20,0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		assert {:split_here} true;
		//||st.Read(0x40)+0x40,0x60,st.Read(0x40)+0x20,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Swap(st,2);
		//||st.Read(0x40)+0x20,0x60,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Pop(st);
		//||0x60,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Dup(st,1);
		//||0x60,0x60,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := MLoad(st);
		assert st.Peek(0) == st.Read(0x60);
		//||st.Read(0x60),0x60,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		assert st.Peek(0) <= 0xffff;
		assert st'.Peek(1) + 0x20 == st.Peek(2);
		assert (MAX_U256 as u256- 0xffff) >= st.Peek(2);
		st := block_0_0x00e7(st);
		return st;
	}

	method block_0_0x00e7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00e7
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x0d && st'.Peek(1) == st'.Peek(5) == 0x60 && st'.Peek(2) == 0xe0 && st'.Peek(3) == st'.Peek(4) == 0xa0 && st'.Peek(6) == 0xcc)
  	
	{
		var st := st';
		//||st.Read(0x60),0x60,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Swap(st,1);
		//||0x60,st.Read(0x60),st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		st := Push1(st,0x20);
		//||0x20,0x60,st.Read(0x60),st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,nam|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||0x80,st.Read(0x60),st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Swap(st,1);
		//||st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert st.Peek(0) == st'.Peek(0);
		st := Dup(st,1);
		//||st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,4);
		//||st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,4);
		//||0x80,st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Push1(st,0x00);
		assert st.Peek(3) == st'.Peek(0);
		assert st.Peek(6) == st'.Peek(2);
		assert st.Peek(3) == st.Peek(4);
		//||0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert st.Peek(6) <= (MAX_U256 as u256) - st.Peek(4);
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
	
	requires st'.Peek(0) as nat == i as nat * 0x20 <= 0x0d as nat + 0x1f
	requires i > 0 ==>  st'.MemSize() >= 0x100 && st'.Read(0xe0) == st'.Read(0x80)
	
	// Static stack items
	requires (st'.Peek(1) == 0x80 && st'.Peek(2) == 0xe0 && st'.Peek(3) == st'.Peek(4) == 0x0d
			&& st'.Peek(5) == 0x80 && st'.Peek(6) == 0xe0 && st'.Peek(7) == st'.Peek(8) == 0xa0
			&& st'.Peek(9) == 0x60 && st'.Peek(10) == 0xcc)
	
	// Termination
	decreases (st'.Read(0x60)+0x1f) - i*0x20,2
	
	{
		var st := st';
		//||0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := JumpDest(st);
		//||0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,4);
		//||st.Read(0x60),0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Dup(st,2);
		//||0x00,st.Read(0x60),0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Lt(st); // y < x
		//||0x00<st.Read(0x60),0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		
		st := IsZero(st);
		//||0x00>=st.Read(0x60),0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Push2(st,0x010c);
		//||0x10c,0x00>=st.Read(0x60),0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60),st.Read(0x60),0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert (st.Peek(2) == i * 0x20 && st.Peek(3) == 0x80 && st.Peek(4) == 0xe0 && st.Peek(5) == st.Peek(6) == 0x0d && st.Peek(7) == 0x80 
				&& st.Peek(8) == 0xe0 && st.Peek(9) == st.Peek(10) == 0xa0 && st.Peek(11) == 0x60 && st.Peek(12) == 0xcc);
		
		assume {:axiom} st.IsJumpDest(0x10c);
		st := JumpI(st);
		if st.PC() == 0x10c { 
			assert i == 1;
			assert (i * 0x20) >= st.Read(0x60); // i.e. initially false
			// ||y,0x80,_,x,b,0x80,a,_,_,0x60,0xcc,name|
			//||0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60)==0,st.Read(0x60)==0,0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
			st := block_0_0x010c(st); 
			return st;
		
		} // if y >= x
		// ||0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		// ||y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		st := Dup(st,1);
		// ||0x00,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		// ||y,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		assert (st.Peek(2) == 0x80 && st.Peek(3) == 0xe0 && st.Peek(4) == st.Peek(5) == 0x0d
			&& st.Peek(6) == 0x80 && st.Peek(7) == 0xe0 && st.Peek(8) == st.Peek(9) == 0xa0
			&& st.Peek(10) == 0x60 && st.Peek(11) == 0xcc);
		assert st.Peek(0) == st.Peek(1)  == i * 20;
		st := block_0_0x00fb(i,st); // i.e. y < x
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
	requires st'.Peek(0) as nat == st'.Peek(1) as nat == i as nat * 0x20 < 0x0d as nat 
	requires (st'.Peek(2) == 0x80 && st'.Peek(3) == 0xe0 && st'.Peek(4) == st'.Peek(5) == 0x0d
			&& st'.Peek(6) == 0x80 && st'.Peek(7) == 0xe0 && st'.Peek(8) == st'.Peek(9) == 0xa0
			&& st'.Peek(10) == 0x60 && st'.Peek(11) == 0xcc)

	// Termination
	decreases st'.Read(0x60) - i*20,3
	{
		var st := st';
		// |i,i,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,name|
		st := Dup(st,3);
		// ||0x80,i,i,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		assert {:split_here} true;
		// ||0x80+i,i,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,name|
		assert st.Peek(0) == 0x80 + (i*0x20);
		assert (st.Peek(1) == i*0x20 && st.Peek(2) == 0x80 && st.Peek(3) == 0xe0 && st.Peek(4) == st.Peek(5) == 0x0d
			&& st.Peek(6) == 0x80 && st.Peek(7) == 0xe0 && st.Peek(8) == st.Peek(9) == 0xa0
			&& st.Peek(10) == 0x60 && st.Peek(11) == 0xcc);
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
	requires st'.Peek(1) as nat == i as nat * 0x20 < 0x0d as nat 
	requires (st'.Peek(0) == 0x80 + (i*0x20) && st'.Peek(2) == 0x80 && st'.Peek(3) == 0xe0 && st'.Peek(4) == st'.Peek(5) == 0x0d
			&& st'.Peek(6) == 0x80 && st'.Peek(7) == 0xe0 && st'.Peek(8) == st'.Peek(9) == 0xa0
			&& st'.Peek(10) == 0x60 && st'.Peek(11) == 0xcc)
	
	// Termination
	decreases st'.Read(0x60) - i*0x20,2
	{
		var st := st';
		// ||0x80+i,i,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,name|
		st := MLoad(st);
		// ||st.Read(0x80+i),i,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,name|
		assert i == 0 ==> st.Peek(0) == st.Read(0x80);
		st := Dup(st,2);
		// ||0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// ||y,mem(y+0x80),y,0x80,z,x,_,0x80,_,_,_,0x60,0xcc,name|
		st := Dup(st,5);
		// ||_,0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// ||z,y,mem(y+0x80),y,0x80,z,x,_,0x80,_,_,_,0x60,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		assert {:split_here} true;
		// ||_,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// ||z+y,mem(y+0x80),y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		assert st.Peek(0) == 0xe0 + (i*0x20);
		assert st.Peek(2) == i*0x20;
		assert i == 0 ==> st.Peek(1) == st'.Read(0x80);
		// assert (st.Peek(3) == 0x80 && st.Peek(4) == 0xe0 && st.Peek(5) == st.Peek(6) == 0x0d
		// 	&& st.Peek(7) == 0x80 && st.Peek(8) == 0xe0 && st.Peek(9) == st.Peek(10) == 0xa0
		// 	&& st.Peek(11) == 0x60 && st.Peek(12) == 0xcc);
		st := MStore(st);
		assert {:split_here} true;
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// ||y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		st := Push1(st,0x20);
		// // ||0x20,y,0x80,_,x,x,0x80,_,_,_,0x60,0xcc,name|
		assert (st.Peek(0) == 0x20 && st.Peek(2) == 0x80 && st.Peek(3) == 0xe0 && st.Peek(4) == st.Peek(5) == 0x0d
			&& st.Peek(6) == 0x80 && st.Peek(7) == 0xe0 && st.Peek(8) == st.Peek(9) == 0xa0
			&& st.Peek(10) == 0x60 && st.Peek(11) == 0xcc);
		assert st.Peek(1) == i * 0x20;
		st := block_0_0x0104(i,st);
		return st;
	}

	method block_0_0x0104(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0104
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x0d
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	requires i == 0 ==>  st'.Read(0xe0) == st'.Read(0x80) 
		// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires st'.Peek(1) as nat == i as nat * 0x20 < 0x0d as nat 
	requires (st'.Peek(0) == 0x20 && st'.Peek(2) == 0x80 && st'.Peek(3) == 0xe0 && st'.Peek(4) == st'.Peek(5) == 0x0d
			&& st'.Peek(6) == 0x80 && st'.Peek(7) == 0xe0 && st'.Peek(8) == st'.Peek(9) == 0xa0
			&& st'.Peek(10) == 0x60 && st'.Peek(11) == 0xcc)
	// Termination
	decreases st'.Read(0x60) - i*0x20,1
	{
		var st := st';
		// ||0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// ||0x20,y,0x80,_,x,x,0x80,z,_,_,0x60,0xcc,name|
		st := Dup(st,2);
		// ||0x00,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// ||y,0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		// Havoc 0
		// ||_,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// ||y,0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		assert st.Peek(0) as nat == i as nat * 0x20 < 0x0d as nat;
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//assert {:split_here} true;
		assert st.Peek(0) == (i*0x20)+0x20;
		//||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// Havoc 0
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// ||y+0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		st := Swap(st,1);
		// ||0x00,_,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,name|
		// ||y,y+0x20,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		st := Pop(st);
		// ||y+0x20,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		st := Push2(st,0x00f1);
		// ||0xf1,y+0x20,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0xf1);
		st := Jump(st);
		// ||y+0x20,0x80,_,x,x,0x80,z,_,_,0x60,0xcc,name|
		assert (st.Peek(1) == 0x80 && st.Peek(2) == 0xe0 && st.Peek(3) == st.Peek(4) == 0xd
			&& st.Peek(5) == 0x80 && st.Peek(6) == 0xe0 && st.Peek(7) == st.Peek(8) == 0xa0
			&& st.Peek(9) == 0x60 && st.Peek(10) == 0xcc);
		assert st.Peek(0) == (i*0x20)+0x20 == (i+1) * 0x20;
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
									&& st'.Read(0xe0) == st'.Read(0x80) 
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires (st'.Peek(4) == 0x0d && st'.Peek(6) == 0xe0 && st'.Peek(7) == st'.Peek(8) == 0xa0 && st'.Peek(9) == 0x60 && st'.Peek(10) == 0xcc)

	
	{
		var st := st';
		//||0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60)==0,st.Read(0x60)==0,0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := JumpDest(st);
		//||0x00,0x80,st.Read(0x40)+0x40,st.Read(0x60)==0,st.Read(0x60)==0,0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Pop(st);
		//||0x80,st.Read(0x40)+0x40,st.Read(0x60)==0,st.Read(0x60)==0,0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|	
		st := Pop(st);
		//||st.Read(0x40)+0x40,st.Read(0x60)==0,st.Read(0x60)==0,0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert st.Operands() == 10;
		st := Pop(st);
		//||st.Read(0x60)==0,st.Read(0x60)==0,0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Pop(st);
		//||st.Read(0x60)==0,0x80,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Swap(st,1);
		//||0x80,st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Pop(st);
		//||st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Swap(st,1);
		//||st.Read(0x40)+0x40,st.Read(0x60)==0,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
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
									&& st'.Read(0xe0) == st'.Read(0x80) 
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(0) == 0xe0 && st'.Peek(1) == 0x0d && st'.Peek(2) == st'.Peek(3) == 0xa0 && st'.Peek(4) == 0x60 && st'.Peek(5) == 0xcc)
	
	{
		var st := st';
		//||0xe0,0xd,0xa0,0xa0,0x60,0xcc,name|
		st := Dup(st,2);
		//||0xd,0xe0,0xd,0xa0,0xa0,0x60,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||0xed,0xd,0xa0,0xa0,0x60,0xcc,name|
		assert {:split_here} true;
		assert (st.Peek(0) == 0xed && st.Peek(1) == 0x0d && st.Peek(2) == st.Peek(3) == 0xa0 && st.Peek(4) == 0x60 && st.Peek(5) == 0xcc);
		st := Swap(st,1);
		//||st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Push1(st,0x1f);
		//||0x1f,st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert st.Peek(1) == 0x0d;
		st := AndU5(st);
		//||st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert {:split_here} true;
		assert st.Peek(0) == 0x0d;
		st := Dup(st,1);
		//||st.Read(0x60)==0,st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := IsZero(st);
		assert st.Peek(0) == 0;
		//||0x0,st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		st := Push2(st,0x0139);
		//||0x139,0x0,st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assert (st.Peek(0) == 0x139 && st.Peek(1) == 0 && st.Peek(2) == 0x0d && st.Peek(3) == 0xed && st.Peek(4) == st.Peek(5) == 0xa0 && st.Peek(6) == 0x60 && st.Peek(7) == 0xcc) ;
		st := block_0_0x011f(st);
		return st;
	}

	method block_0_0x011f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x011f
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == st'.Read(0x80) 
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(0) == 0x139 && st'.Peek(1) == 0 && st'.Peek(2) == 0x0d && st'.Peek(3) == 0xed && st'.Peek(4) == st'.Peek(5) == 0xa0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc) 
	
	{
		var st := st';
		//||0x139,0x1,st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0x139);
		st := JumpI(st);
		if st.PC() == 0x139 { 
			assert false; // Dead code i.e. (len % 32) == 0 and since whole words of output, no need for masking of last word of string output
			//||st.Read(0x60)==0,st.Read(0x40)+0x40,st.Read(0x40),st.Read(0x40),0x60,0xcc,name|
			st := block_0_0x0139(st); 
			return st;
		} 
		//||0x1f&b!=0,a+b,_,_,0x60,0xcc,name|
		st := Dup(st,1);
		//||0x1f&b!=0,0x1f+b!=0,a+b,_,_,0x60,0xcc,name|
		st := Dup(st,3);
		//||a+b,0x1f&b!=0,0x1f&b!=0,a+b,_,_,0x60,0xcc,name|
		assert st.Peek(0) == 0xed && st.Peek(1) == 0x0d; 
		assert st.Peek(1) <= st.Peek(0); 
		st := Sub(st);
		assert {:split_here} true;
		assert st.Peek(0) == 0xe0 && st.Peek(1) == 0x0d && st.Peek(5) == 0x60 && st.Peek(6) == 0xcc;
		//||(a+b)-(0x1f&b),0<b<=0xffff,_,_,_,0x60,0xcc,name| i.e. (a+b)-(0x1f&b) == a since b < 0xffff
		st := Dup(st,1);
		//||a,a,*,_,_,_,0x60,0xcc,name|
		st := MLoad(st);
		assert st.Peek(0) == st.Read(0xe0);
		// //||mem(a),a,*,_,_,_,0x60,0xcc,name|
		st := Push1(st,0x01);
		//||0x01,mem(a),a,*,_,_,_,0x60,0xcc,name|
		st := Dup(st,4);
		// //||*,0x01,mem(a),a,*,_,_,_,0x60,0xcc,name|
		//assert st.Peek(0) == 0x0d && st.Peek(1) == 0x1 && st.Peek(2) == st.Read(0xe0) && st.Peek(3) == 0xe0 && st.Peek(5) == 0xe4 && st.Peek(6) == st.Peek(7) == 0xa0  && st.Peek(8) == 0x60 && st.Peek(9) == 0xcc;
		st := block_0_0x0128(st);
		return st;
	}

	method block_0_0x0128(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0128
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == st'.Read(0x80) 
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(0) == 0x0d && st'.Peek(1) == 0x1 && st'.Peek(2) ==st'.Read(0xe0) && st'.Peek(3) == 0xe0 && st'.Peek(6) == st'.Peek(7) == 0xa0 && st'.Peek(8) == 0x60 && st'.Peek(9) == 0xcc)

	{
		var st := st';
		//||len,0x01,st'.Read(0xe0),0xe0,_,_,0xa0,0xa0,0x60,0xcc,name|
		st := Push1(st,0x20);
		//||0x20,len,0x01,st'.Read(0xe0),0xe0,_,_,0xa0,0xa0,0x60,0xcc,name|
		assert st.Peek(0) == 0x20 && st.Peek(1) == 0x0d;
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		assert {:split_here} true;
		//||0x20-*,0x01,#,^,_,_,_,_,0x60,0xcc,name|
		assert (st.Peek(1) == 0x1 && st.Peek(2) == st.Read(0xe0) && st.Peek(3) == 0xe0 && st.Peek(6) == st.Peek(7) == 0xa0 && st.Peek(9) == 0xcc); 
		st := Push2(st,0x0100);
		assert (st.Peek(1) == 0x13);
		st := Exp(st);
		//||e,0x01,#,^,_,_,_,_,0x60,0xcc,name|
		assert st.Peek(1) == 0x01 && st.Peek(2) == st'.Read(0xe0) && st.Peek(3) == 0xe0 ;
		assert st.Peek(6) == st.Peek(7) == 0xa0 && st.Peek(9) == 0xcc;
		assume st.Peek(0) == 0x100000000000000000000000000000000000000 ; // i.e. 2^152
		assert st.Peek(1) <= st.Peek(0);
		st := block_0_0x012f(st);
		return st;
	}

	method block_0_0x012f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x012f
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == st'.Read(0x80) 
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.Peek(0) == 0x100000000000000000000000000000000000000  &&  st'.Peek(2) == st'.Read(0xe0)
	requires (st'.Peek(1) ==  0x01 && st'.Peek(3) == 0xe0 && st'.Peek(6) == st'.Peek(7) == 0xa0 && st'.Peek(9) == 0xcc) 
	{
		var st := st';
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		assert {:split_here} true;
		//||e-1,#,^,_,_,_,_,0x60,0xcc,name|
		assert st.Peek(0) == 0x100000000000000000000000000000000000000 - 0x1 == 0xffffffffffffffffffffffffffffffffffffff;
		st := Not(st);
		//||!(e-1),#,^,_,_,_,_,0x60,0xcc,name|
		assert {:split_here} true;
		assert st.Peek(0) == 0xffffffffffffffffffffffffff00000000000000000000000000000000000000;
		assert st.Peek(1) == st.Read(0xe0) == st.Read(0x80);
		assert st.Peek(1) % 0x100000000000000000000000000000000000000 == 0;
		st := AndUpper13Bytes(st);
		//||st.Read(0xe0),0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		assert st.Peek(0) == st.Read(0xe0) == st.Read(0x80);
		st := Dup(st,2);
		//||0xe0,st.Read(0xe0),0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		st := block_0_0x0133(st);
		return st;
	}

	method block_0_0x0133(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0133
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == st'.Read(0x80) 
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires st'.Peek(0) == 0xe0
	requires st'.Peek(1) == st'.Read(0xe0)
	requires (st'.Peek(2) == 0xe0 && st'.Peek(5) == st'.Peek(6) == 0xa0 && st'.Peek(8) == 0xcc) 

	{
		var st := st';
		//||0xe0,st.Read(0xe0),0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		//assert st.Peek(0) == 0xe0;
		//assert st.Peek(1) == st'.Read(0xe0) ;
		st := MStore(st);
		//||0xe0,len%32,0xed,0xa0,0xa0,*ptr(len),0xcc,name|
		//assert {:split_here} true;
		//assert st.Read(0x80) ==  st'.Read(0x80);
		//assert st.Read(0xe0) == st'.Read(0xe0) == st'.Read(0x80);
		assert st.Peek(0) == 0xe0 && st.Peek(3) == st.Peek(4) == 0xa0 && st.Peek(6) == 0xcc;
		st := block_0_0x0134(st);
		return st;
	}

	method block_0_0x0134(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0134
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == st'.Read(0x80) 
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires  st'.Peek(0) == 0xe0 && st'.Peek(3) == st'.Peek(4) == 0xa0 && st'.Peek(6) == 0xcc
	{
		var st := st';
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
		assert (st.Peek(1) == 0x100 && st.Peek(2) == 0xa0 && st.Peek(5) == 0xcc);
		st := block_0_0x0139(st);
		return st;
	}

	method block_0_0x0139(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0139
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == st'.Read(0x80) 
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(1) == 0x100 && st'.Peek(2) == 0xa0 && st'.Peek(5) == 0xcc)
	{
		var st := st';
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
		//assert st.Peek(0)== st.Read(0x40) <= st.Peek(1);
		st := block_0_0x0142(st);
		return st;
	}

	method block_0_0x0142(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0142
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x0d 
									&& st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x0d
									&& st'.Read(0xe0) == st'.Read(0x80) 
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(0) == 0xa0 && st'.Peek(1) == 0x100 && st'.Peek(2) == 0xcc)

	
	// ensures data := Memory.Slice(st.evm.memory, 0xa0, 0x60);
	// 0000000000000000000000000000000000000000000000000000000000000020 i.e. array starts at pos 32 (the 2nd word)
	// 000000000000000000000000000000000000000000000000000000000000000d i.e. array size of 13 bytes
	// 0x5772617070656420457468657200000000000000000000000000000000000000 i.e. string == "Wrapped Ether"
	
	{
		var st := st';
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
	requires (st'.Peek(0) == 0xcc)
	// Storate Items
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		//|fp=0x0060|0xcc,name|
		st := JumpDest(st);
		//|fp=0x0060|0xcc,name|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0xcc,name|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,0xcc,name|
		st := SLoad(st);
		//|fp=0x0060|st.Load(0)=len*2,0x00,0xcc,name|
		assert st.Peek(0) == st.Load(0x0);
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,len*2,0x00,0xcc,name|
		st := Dup(st,2);
		//|fp=0x0060|len*2,0x01,len*2,0x00,0xcc,name|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,len*2,0x01,len*2,0x00,0xcc,name|
		st := AndU1(st);
		//|fp=0x0060|0,0x01,len*2,0x00,0xcc,name|
		assert st.Peek(0) == st.Load(0x0)%2 && st.Peek(2) == st.Load(0x0);
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
	requires st'.Peek(0) == 0 //i.e. first bit of st'.Load(0x01) which equals 0 since short string
  	requires st'.Peek(2) == st'.Load(0x0)
	requires (st'.Peek(1) == 0x1 && st'.Peek(3) == 0x0 && st'.Peek(4) == 0xcc)
  	// Storate Items
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		//|fp=0x0060|0,0x01,len*2,0x00,0xcc,name|
		st := IsZero(st);
		//|fp=0x0060|1,0x01,len*2,0x00,0xcc,name|
		st := Push2(st,0x0100);
		//|fp=0x0060|0x100,1,0x01,len*2,0x00,0xcc,name|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		//|fp=0x0060|0x100,0x01,len*2,0x00,0xcc,name|
		assert (st.Load(0x0)%2) == 0 ==> st.Peek(1) <= st.Peek(0); // otherwise sub must underflow
		st := Sub(st);
		//|fp=0x0060|0xff,len*2,0x00,0xcc,name|
		assert {:split_here} true;
		assert st.Peek(0) in {MAX_U256 as u256, 0xFF};
		assert st.Peek(1) == st.Load(0x0) && st.Peek(2) == 0x00 && st.Peek(3) == 0xcc;
		
		// ==========================================================
		// NOTE: Reimplemented following to avoid need to reason about bitvector
		// arithmetic.
		// st := And(st);
		if st.Peek(0) == MAX_U256 as u256 { 
			// Masking against MAX_U256 (a nop)
			assert st.Load(0x0)%2 != 0;
			st := st.Pop().Next();
			assert st.Peek(0) == st.Load(0x0);
		} else {
			// Masking against 0xFF
			assert st.Load(0x0)%2 == 0;
			st := AndU8(st);
			assert st.Peek(0) == st.Load(0x0)%256;
		}
		// ==========================================================
		// |fp=0x0060|(len*2)%255,0x00,0xcc,name|
		st := Push1(st,0x02);
		// |fp=0x0060|0x02,(len*2)%256,0x00,0xcc,name|
		st := Swap(st,1);
		// |fp=0x0060|(len*2)%256,0x02,0x00,0xcc,name|
		assert st.Peek(1) != 0;
		st := Div(st);
		// |fp=0x0060|len=0xd,0x00,0xcc,name|
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
	requires (st'.Peek(0) == 0xd && st'.Peek(1) == 0x0 && st'.Peek(2) == 0xcc)
	
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		// |fp=0x0060|len=0xd,0x00,0xcc,name|
		st := Dup(st,1);
		// |fp=0x0060|len,len,0x00,0xcc,name|
		st := Push1(st,0x1f);
		// |fp=0x0060|0x1f,len,len,0x00,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |fp=0x0060|len+0x1f=0x2c,len,0x00,0xcc,name|
		assert (st.Peek(0) == 0x2c && st.Peek(1) == 0xd && st.Peek(2) == 0x0 && st.Peek(3) == 0xcc);

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
		assert (st.Peek(0) == 0x20 && st.Peek(1) == 0xd && st.Peek(2) == 0x0 && st.Peek(3) == 0xcc);
		
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
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0xd && st'.Peek(2) == 0x0 && st'.Peek(3) == 0xcc)
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		// |fp=0x0060|0x20,len,0x00,0xcc,name|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,*,len,0x00,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |fp=0x0060|*+0x20,len,0x00,0xcc,name|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,*+0x20,len,0x00,0xcc,name|
		st := MLoad(st);
		// |fp=0x0060|fmp=Read(0x40),*+0x20,len,0x00,0xcc,name|
		assert st.Peek(2) == 0xd;
		st := Swap(st,1);
		// |fp=0x0060|*+0x20,fmp,len,0x00,0xcc,name|
		st := Dup(st,2);
		// |fp=0x0060|fmp,*+0x20,fmp,len,0x00,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |fp=0x0060|fmp+*+0x20,fmp,len,0x00,0xcc,name|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,fmp+*+0x20,fmp,len,0x00,0xcc,name|
		assert (st.Peek(0) == 0x40 && st.Peek(1) == 0xa0 && st.Peek(2) == 0x60 && st.Peek(3) == 0xd && st.Peek(4) == 0x0 && st.Peek(5) == 0xcc);
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
	requires (st'.Peek(0) == 0x40 && st'.Peek(1) == 0xa0 && st'.Peek(2) == 0x60 && st'.Peek(3) == 0x0d &&st'.Peek(4) == 0x0 && st'.Peek(5) == 0xcc)
	
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		// |fp=0x0060|0x40,fmp+*+0x20,fmp,len,0x00,0xcc,name|
		st := MStore(st);
		// |fp=0x0060|fmp',len,0x00,0xcc,name| i.e. st.Read(0x40) == fmp+*+0x20, fmp' refers to previous fmp == 0x60
		assert st.Read(0x40) == st'.Peek(1);
		st := Dup(st,1);
		// ||fmp',fmp',len,0x00,0xcc,name|
		st := Swap(st,3);
		// ||0x00,fmp',len,fmp',0xcc,name|
		st := Swap(st,2);
		// ||len,fmp',0x00,fmp',0xcc,name|
		st := Swap(st,1);
		// ||fmp',len,0x00,fmp',0xcc,name|
		st := Dup(st,2);
		// ||len,fmp',len,0x00,fmp',0xcc,name|
		st := Dup(st,2);
		// ||fmp',len,fmp',len,0x00,fmp',0xcc,name|
		st := MStore(st);		
		// ||0x60,len,0x00,0x60,0xcc,name| i.e. st.Read(0x60) == len
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
	requires (st'.Peek(0) == 0x60 && st'.Peek(1) == 0x0d && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x60 && st'.Peek(4) == 0xcc)
  	
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
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
		assert (st.Peek(0) == 0x1 && st.Peek(1) == st.Peek(3) == st.Load(0x0) && st.Peek(2) == 0x1 && st.Peek(4) == 0x0 && st.Peek(5) == 0x80 && st.Peek(6) == 0xd && st.Peek(7) == 0x0 && st.Peek(8) == 0x60 && st.Peek(9) == 0xcc);
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
	requires (st'.Peek(0) == 0x1 && st'.Peek(1) == st'.Peek(3) == st'.Load(0x0) && st'.Peek(2) == 0x1 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0x80 && st'.Peek(6) == 0xd && st'.Peek(7) == 0x0 && st'.Peek(8) == 0x60 && st'.Peek(9) == 0xcc)
  	//requires st'.Peek(3) == st'.Load(1)
  	// Termination
	//requires (st'.Read(0x60) <= 0xffff)
  	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	
	{
		var st := st';
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
		assert st.Peek(1) == 0x01 && st.Peek(2) == st.Load(0) && st.Peek(3) == st.Peek(6) == 0x00  && st.Peek(4) == 0x80 
				&& st.Peek(7) == 0x60 && st.Peek(8) == 0xcc;
		assert st.Peek(5) == st'.Peek(6); //(st.Load(0)% 256)/2 || st.Peek(5) == st'.Load(0)/2;

		assert (st.Load(0x0)%2) == 0 ==> st.Peek(1) <= st.Peek(0); // otherwise sub must underflow
		st := Sub(st);
		assert {:split_here} true;
		assert st.Peek(0) in {MAX_U256 as u256, 0xFF};
		// ||0xff,st.Load(0),0x00,0x80,len,0x00,0x60,0xcc,name|
		// ==========================================================
		// NOTE: Reimplemented following to avoid need to reason about bitvector
		// arithmetic.
		//st := And(st);
		if st.Peek(0) == MAX_U256 as u256 { 
			// Masking against MAX_U256 (a nop)
			assert st.Load(0x0)%2 != 0;
			st := st.Pop().Next();
			assert st.Peek(0) == st.Load(0x0);
		} else {
			// Masking against 0xFF
			assert st.Load(0x0)%2 == 0;
			st := AndU8(st);
			assert st.Peek(0) == 0x01a;
		}
		// ==========================================================
		// ||st.Load(0)*,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert (st.Load(0x0)%2 != 0 && st.Peek(0) == st.Load(0)) || (st.Load(0x0)%2 == 0 && st.Peek(0) == st.Load(0)%256);
		
		st := Push1(st,0x02);
		// ||0x02,st.Load(0)*,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Swap(st,1);
		// ||st.Load(0)*,0x02,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert (st.Peek(0) == 0x1a && st.Peek(1) == 0x02 && st.Peek(2) == 0x0 && st.Peek(3) == 0x80 
				&& st.Peek(5) == 0x0 && st.Peek(6) == 0x60 && st.Peek(7) == 0xcc);
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
	requires (st'.Peek(0) == 0x1a && st'.Peek(1) == 0x2 && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 
				&& st'.Peek(4) == 0x0d && st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
  
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		// ||len*2,0x02,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert st.Peek(1) != 0;
		st := Div(st);
		// ||len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert st.Peek(0) == (st.Load(0)% 256)/2 || st.Peek(0) == st.Load(0)/2;
		assert st.Peek(0) == st.Peek(3);
		st := Dup(st,1);
		// ||len,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := IsZero(st);
		// ||len==0,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Push2(st,0x0573);
		// ||0x573,len==0,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert (st.Peek(3) == st.Peek(6) == 0x0 && st.Peek(4) == 0x80 && st.Peek(2) == st.Peek(5) && st.Peek(7) == 0x60 && st.Peek(8) == 0xcc);
		assume {:axiom} st.IsJumpDest(0x573);
		st := JumpI(st);
		if st.PC() == 0x573 { 
			assert false;
			// ||len,0x00,0x80,len,0x00,0x60,0xcc,name|
			st := block_0_0x0573(st); 
			return st;
		} 
		// ||len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert st.Peek(0) == st.Peek(3) != 0;
		assert ((st.Load(0x0)%2 == 0) && ((st.Load(0x0) % 256) /2 != 0) )|| ((st.Load(0x0)%2 != 0) && (st.Load(0x0) > 2));
		st := Dup(st,1);
		// ||len,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Push1(st,0x1f);
		// ||0x1f,len,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Lt(st);
		// ||0x1f<len,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert (st.Peek(2) == st.Peek(5) == 0x0 && st.Peek(3) == 0x80 && st.Peek(1) == st.Peek(4) && st.Peek(6) == 0x60 && st.Peek(7) == 0xcc);
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
  	requires (st'.Peek(0) == 0 && st'.Peek(1) == 0x0d && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 
			&& st'.Peek(4) == 0x0d && st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
  
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
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
		assert st.Peek(0) <= 0x1f; // i.e. len <= 0x1f
		st := Push2(st,0x0100);
		// ||0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
    	assert st.Peek(0) == 0x100 && st.Peek(1) == st.Peek(4) && st.Peek(2) == st.Peek(5) ==0x00 && st.Peek(3) == 0x80 && st.Peek(6) == 0x60 && st.Peek(7) == 0xcc;
		st := Dup(st,1);
		// ||0x100,0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Dup(st,4);
		// ||0x00,0x100,0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := SLoad(st);
    	// ||st.Load(0),0x100,0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert (st.Peek(1) == st.Peek(2) == 0x100 && st.Peek(3) == st.Peek(6) 
				&& st.Peek(4) == st.Peek(7) == 0x0 && st.Peek(5) == 0x80 && st.Peek(8) == 0x60 && st.Peek(9) == 0xcc);
		
		assert st.Peek(1) != 0;
		st := Div(st);
		// ||st.Load(0)/0x100,0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert st.Peek(0) == st.Load(0)/0x100;
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		assert {:split_here} true;
		// ||st.Load(0)/0x100*0x100,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		assert (st.Peek(1) == st.Peek(4) && st.Peek(2) == st.Peek(5) == 0x0 && st.Peek(3) == 0x80 && st.Peek(6) == 0x60 && st.Peek(7) == 0xcc);
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
	requires (st'.Peek(0) == 0x5772617070656420457468657200000000000000000000000000000000000000 && st'.Peek(1) == 0xd && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 
			&& st'.Peek(4) == 0xd && st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)

	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		// ||(st.Load(0x0)>>8)<<8,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := Dup(st,4);
		// ||0x80,(st.Load(0x0)>>8)<<8,len,0x00,0x80,len,0x00,0x60,0xcc,name|
		st := MStore(st);
		//assert {:split_here} true;
		// ||len,0x00,0x80,len,0x00,0x60,0xcc,name| st.Read(0x80) == 0
		assert st.Read(0x80) == st'.Peek(0);
		st := Swap(st,2);
		// ||0x80,0x00,0xd,0xd,0x00,0x60,0xcc,name|
		st := Push1(st,0x20);
		// ||0x20,0x80,0x00,0xd,0xd,0x00,0x60,0xcc,name|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0xa0,0x00,0xd,0xd,0x00,0x60,0xcc,name|
		assert {:split_here} true;
		assert (st.Peek(5) == 0x60 && st.Peek(6) == 0xcc);
		st := Swap(st,2);
		// ||0xd,0x00,0xa0,0xd,0x00,0x60,0xcc,name|
		st := Push2(st,0x0573);
		// ||0x573,0xd,0x00,0xa0,0xd,0x00,0x60,0xcc,name|
		assume {:axiom} st.IsJumpDest(0x573);
		st := Jump(st);
		// ||0xd,0x00,0xa0,0xd,0x00,0x60,0xcc,name|
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
	// // Static stack items
	// requires (st'.Peek(1) == st'.Peek(4) == 0x0 && st'.Peek(2) == 0x80 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	// requires 0x1f <= st'.Peek(0) < 0xff7f //== st'.Peek(3) //
	// {
	// 	var st := st';
	// 	// ||len,0x00,0x80,len,0x00,0x60,0xcc,name|
	// 	st := JumpDest(st);
	// 	// ||len,0x00,0x80,len,0x00,0x60,0xcc,name|
	// 	st := Dup(st,3);
	// 	// ||0x80,len,0x00,0x80,len,0x00,0x60,0xcc,name|
	// 	assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
	// 	st := Add(st);
	// 	// ||0x80+len,0x00,0x80,len,0x00,0x60,0xcc,name|
	// 	var n := st.Peek(0);
	// 	assert 0x9f <= n < 0xffff;
	// 	st := Swap(st,2);
	// 	//assert {:split_here} true;
	// 	// ||0x80,0x00,n,len,0x00,0x60,0xcc,name|
	// 	st := Swap(st,1);
	// 	// ||0x00,0x80,n,len,0x00,0x60,0xcc,name|
	// 	st := Push1(st,0x00);
	// 	// ||0x00,0x00,0x80,n,len,0x00,0x60,0xcc,name|
	// 	assert st.Peek(7) == 0xcc;
	// 	st := MStore(st);
	// 	assert {:split_here} true;
	// 	assert st.Read(0x00) == 0x00;
	// 	// ||0x80,n,len,0x00,0x60,0xcc,name|
	// 	st := Push1(st,0x20);
	// 	// ||0x20,0x80,n,len,0x00,0x60,0xcc,name|
	// 	assert (st.Peek(0) == 0x20 && st.Peek(1) == 0x80 && st.Peek(4) == 0x0 && st.Peek(5) == 0x60 && st.Peek(6) == 0xcc);
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
	// // Static stack items
	// requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x80 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	// requires (0x80 <= st'.Peek(2) == n < 0xffff)
	// {
	// 	var st := st';
	// 	// ||0x20,0x80,n,len,0x00,0x60,0xcc,name|
	// 	st := Push1(st,0x00);
	// 	// ||0x00,0x20,0x80,n,len,0x00,0x60,0xcc,name|
	// 	st := Keccak256(st); // sha3(st.Read(0x00))
	// 	// ||Hash(0x0),0x80,n,len,0x00,0x60,0xcc,name|
	// 	st := Swap(st,1);
	// 	// ||0x80,Hash(0x0),n,len,0x00,0x60,0xcc,name|
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
	// // Static stack items
	// requires (st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	// requires (st'.Peek(0) == i && st'.Peek(2) == n)
	// //requires st'.Peek(1) <= (MAX_U256 as u256 - 2)
	// // Termination
	// requires 0x80 <= i <= n < 0xffff
	// decreases n-i,2
	// {
	// 	var st := st';
	// 	// ||i=0x80,Hash(0x0),n,len,0x00,0x60,0xcc,name|
	// 	st := JumpDest(st);
	// 	// ||i,Hash(0x0),n,len,0x00,0x60,0xcc,name|
	// 	st := Dup(st,2);
	// 	// ||Hash(0x0),i,Hash(0x0),n,len,0x00,0x60,0xcc,name|
	// 	st := SLoad(st);
	// 	// ||st.Load(Hash(0x0)),i,Hash(0x0),n,len,0x00,0x60,0xcc,name|
	// 	assert {:split_here} true;
	// 	st := Dup(st,2);
	// 	// ||i,st.Load(Hash(0x0)),i,Hash(0x0),n,len,0x00,0x60,0xcc,name|
	// 	st := MStore(st);
	// 	assert {:split_here} true; //i.e st.Read(i=0x80) == st.Load(Hash(0x0));
	// 	// ||i,Hash(0x0),n,len,0x00,0x60,0xcc,name|
	// 	st := Swap(st,1);
	// 	// ||Hash(0x0),i,n,len,0x00,0x60,0xcc,name|
	// 	st := Push1(st,0x01);
	// 	// ||0x01,Hash(0x0),i,n,len,0x00,0x60,0xcc,name|
	// 	assume (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256); // Hash(0x0) + 1 is never used and therefore doesn't matter if it overflows
	// 	st := Add(st);
	// 	// ||Hash(0x0)+1,i,n,len,0x00,0x60,0xcc,name|
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
	// // Static stack items
	// requires (st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	// requires (st'.Peek(1) == i && st'.Peek(2) == n)
	// //requires st'.Peek(0) <= (MAX_U256 as u256 - 1)
	// // Termination
	// requires 0x80 <= i <= n < 0xffff
	// decreases n-i,1
	// {
	// 	var st := st';
	// 	// ||Hash(0x0)+1,i,n,len,0x00,0x60,0xcc,name|
	// 	st := Swap(st,1);
	// 	// ||i,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := Push1(st,0x20);
	// 	// ||0x20,i,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
    // 	assert st.Peek(7) == st'.Peek(6) == 0xcc;
	// 	assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
	// 	st := Add(st);
	// 	// ||i+0x20,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := Dup(st,1);
	// 	// ||i+0x20,i+0x20,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := Dup(st,4);
	// 	// ||n,i+0x20,i+0x20,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := Gt(st);
	// 	// ||n>(i+0x20),i+0x20,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
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
	// // Static stack items
	// requires (st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	// requires (st'.Peek(0) in {0,1}) && (st'.Peek(0) == 0 <==> n <= i)
	// requires (st'.Peek(1) == i && st'.Peek(3) == n)
	// //requires st'.Peek(2) <= (MAX_U256 as u256 - 1)
	// // Termination
	// requires n < 0xffff && 0xA0 <= i <= (n+0x20)
	// decreases n+0x20-i,0
	// {
	// 	var st := st';
	// 	// ||n>(i+0x20),i+0x20,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	// ||n>i,i,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := Push2(st,0x0556);
	// 	// ||0x556,n>i,i,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	assume {:axiom} st.IsJumpDest(0x556);
	// 	st := JumpI(st);
	// 	if st.PC() == 0x556 { 
	// 		// ||i,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 		// as n > i
	// 		//assert st'.Peek(0) == 1; // probably don't need these, leaving for tidy up, i.e. n > i+0x20
	// 		st := block_0_0x0556(i,n,st); 
	// 		return st; 
	// 		}
	// 	//n <= i
	// 	// ||i,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := Dup(st,3);
	// 	// ||n,i,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	assert (st.Peek(5) == 0x0 && st.Peek(6) == 0x60 && st.Peek(7) == 0xcc);
	// 	st := Swap(st,1);
	// 	assert st.Peek(5) == 0x00;
	// 	// ||i,n,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	assert st.Peek(1) <= st.Peek(0);
	// 	st := Sub(st);
	// 	//||i-n,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := Push1(st,0x1f);
	// 	//||0x1f,i-n,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := AndU5(st);
	// 	//||(i-n)%32,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := Dup(st,3);
	// 	//||n,(i-n)%32,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
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
	// // Static stack items
	// requires (st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	// requires (st'.Peek(0) as nat + st'.Peek(1) as nat) <= (MAX_U256)
	// {
	// 	var st := st';
	// 	//||n,(i-n)%32,Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
	// 	st := Add(st);
	// 	//||n+((i-n)%32),Hash(0x0)+1,n,len,0x00,0x60,0xcc,name|
	// 	st := Swap(st,2);
	// 	//||n,Hash(0x0)+1,n+((i-n)%32),len,0x00,0x60,0xcc,name|
	// 	st := block_0_0x0573(st);
	// 	return st;
	// }

	method block_0_0x0573(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0573
	// Free memory pointer
	requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 
	requires st'.Read(0x60) == 0x0d  && st'.Read(0x80) == 0x5772617070656420457468657200000000000000000000000000000000000000
	//requires st'.Read(0x60) > 0x1f ==> st'.Read(0x80) == st'.Load(Hash(0x1))

	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
  	
	{
		var st := st';
		//||len,0x00,0xa0,len,0x00,0x60,0xcc,name| i.e. from path where len < 31
		//||n,Hash(0x0)+1,n+((i-n)%32),len,0x00,0x60,0xcc,name| i.e. from path where len >= 31
		st := JumpDest(st);
		//||n,Hash(0x0)+1,n+((i-n)%32),len,0x00,0x60,0xcc,name|
		st := Pop(st);
		//||Hash(0x0)+1,n+((i-n)%32),len,0x00,0x60,0xcc,name|
		st := Pop(st);
		//||n+((i-n)%32),len,0x00,0x60,0xcc,name|
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
		st := block_0_0x00cc(st);
		return st;
	}

}
