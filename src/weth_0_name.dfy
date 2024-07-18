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
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		//|fp=0x0060|callSig|
		st := JumpDest(st);
		//|fp=0x0060|callSig|
		st := CallValue(st);
		//|fp=0x0060|callVal,callSig|
		st := IsZero(st);
		//|fp=0x0060|callVal==0,callSig|
		st := Push2(st,0x00c4);
		//|fp=0x0060|0x2ed,callVal==0,callSig|
		assume {:axiom} st.IsJumpDest(0xc4);
		st := JumpI(st);
		if st.PC() == 0xc4 { st := block_0_0x00c4(st); return st;} // call value is zero
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_|
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
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		//|fp=0x0060|callSig|
		st := JumpDest(st);
		//|fp=0x0060|callSig|
		st := Push2(st,0x00cc);
		//|fp=0x0060|0xcc,callSig|
		st := Push2(st,0x04dd);
		//|fp=0x0060|0x4dd,0xcc,callSig|
		assume {:axiom} st.IsJumpDest(0x4dd);
		st := Jump(st);
		//|fp=0x0060|0xcc,callSig|
		st := block_0_0x04dd(st);
		return st;
	}

	method block_0_0x00cc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00cc
	// Free memory pointer
	requires st'.MemSize() >= 0x80 //&& st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x04
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(1) == 0xcc)	
	{
		var st := st';
		//||0x60,0xcc,_|
		st := JumpDest(st);
		//||0x60,0xcc,_|
		st := Push1(st,0x40);
		//||0x40,0x60,0xcc,_|
		st := MLoad(st);
		//||_,0x60,0xcc,_|
		st := Dup(st,1);
		//||_,_,0x60,0xcc,_|
		st := Dup(st,1);
		//||_,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		//||0x20,_,_,_,0x60,0xcc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,_,_,_,0x60,0xcc,_|
		st := Add(st);
		//||_,_,_,0x60,0xcc,_|
		st := Dup(st,3);
		st := block_0_0x00d6(st);
		return st;
	}

	method block_0_0x00d6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00d6
	// Stack height(s)
	requires st'.Operands() == 7
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	requires st'.Read(0x40) == st'.Peek(0)
	// Static stack items
	requires (st'.Peek(4) == 0x60 && st'.Peek(5) == 0xcc)
	requires (st'.Peek(0) == st'.Peek(2) == st'.Peek(3))	
	requires (st'.Read(0x60) <= 0xffff)
	requires var p := st'.Peek(0); p >= 0x80
	requires var q := st'.Peek(1); var p := st'.Peek(0); q > p && q - p == 0x20
	
	{
		var st := st';
		//||_,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		//||_,_,_,_,_,0x60,0xcc,_|
		assert st.Peek(1) <= st.Peek(0);
		//||_,_,_,_,_,0x60,0xcc,_|
		st := Sub(st);
		//||_,_,_,_,0x60,0xcc,_|
		st := Dup(st,3);
		//||_,_,_,_,_,0x60,0xcc,_|
		st := MStore(st);
		//||_,_,_,0x60,0xcc,_|
		st := Dup(st,4);
		//||0x60,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		//||_,0x60,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		//||0x60,_,0x60,_,_,_,0x60,0xcc,_|
		st := MLoad(st);
		st := block_0_0x00de(st);
		return st;
	}

	method block_0_0x00de(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00de
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x60 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	requires (st'.Read(0x60) <= 0xffff)
	// Termination	
	requires var p := st'.Peek(1); (MAX_U256 as u256 - 0x1001f) >= p >= 0x80
	{
		var st := st';
		//||_,p,0x60,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		//||p,_,p,0x60,_,_,_,0x60,0xcc,_|
		st := MStore(st);
		//||p,0x60,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		//||0x20,p,0x60,_,_,_,0x60,0xcc,_|
		st := block_0_0x00e2(st);
		return st;
	}

	method block_0_0x00e2(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00e2
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(0) == 0x20 &&  st'.Peek(2) == 0x60 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	requires (st'.Read(0x60) <= 0xffff)
	//b <= 0xffff && a <= max - b
	// Termination	
	requires var p := st'.Peek(1); (MAX_U256 as u256- 0x1001f) >= p >= 0x80
	{
		var st := st';
		//||0x20,_,0x60,_,_,_,0x60,0xcc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,a-0x20,0x60,_,_,_,0x60,0xcc,_|
		st := Add(st);
		assert {:split_here} true;
		//||a,0x60,_,_,_,0x60,0xcc,_|
		st := Swap(st,2);
		//||_,0x60,a,_,_,0x60,0xcc,_|
		st := Pop(st);
		//||0x60,a,_,_,0x60,0xcc,_|
		st := Dup(st,1);
		//||0x60,0x60,a,_,_,0x60,0xcc,_|
		st := MLoad(st);
		assert st.Peek(0) == st.Read(0x60);
		//||b,0x60,a,_,_,0x60,0xcc,_|
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
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires var x := st'.Peek(0); x == st'.Read(0x60) <= 0xffff
	requires (st'.Peek(1) == 0x60 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	requires var x := st'.Peek(0); var y := st'.Peek(2); y <= (MAX_U256 as u256) - x
	{
		var st := st';
		//||b,0x60,a,_,_,0x60,0xcc,_|
		st := Swap(st,1);
		//||0x60,b,a,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		//||0x20,0x60,b,a,_,_,0x60,0xcc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||0x20,0x60,b,a,_,_,0x60,0xcc,_|
		st := Add(st);
		//||0x80,b,a,_,_,0x60,0xcc,_|
		st := Swap(st,1);
		//||b,0x80,a,_,_,0x60,0xcc,_|
		assert st.Peek(0) == st'.Peek(0);
		st := Dup(st,1);
		//||b,b,0x80,a,_,_,0x60,0xcc,_|
		st := Dup(st,4);
		//||_,b,b,0x80,a,_,_,0x60,0xcc,_|
		st := Dup(st,4);
		//||0x80,_,b,b,0x80,a,_,_,0x60,0xcc,_|
		st := Push1(st,0x00);
		assert st.Peek(3) == st'.Peek(0);
		assert st.Peek(6) == st'.Peek(2);
		assert st.Peek(3) == st.Peek(4);
		// ||0x00,0x80,_,b,b,0x80,a,_,_,0x60,0xcc,_|
		assert st.Peek(6) <= (MAX_U256 as u256) - st.Peek(4);
		st := block_0_0x00f1(0,st);
		return st;
	}

	method block_0_0x00f1(i: nat, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00f1
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires (st'.Peek(1) == 0x80 && st'.Peek(5) == 0x80 && st'.Peek(9) == 0x60 && st'.Peek(10) == 0xcc)	
	requires (st'.Peek(3) == st'.Peek(4))
	// Termination
	requires var y := st'.Peek(0); y as nat == i * 0x20
	requires var x := st'.Peek(3); x <= 0xffff
	requires var x := st'.Peek(3); var y := st'.Peek(0); y <= (x+0x1f)
	requires var x := st'.Peek(4); var y := st'.Peek(6); y <= (MAX_U256 as u256) - x
	decreases var x := st'.Peek(3); var y := st'.Peek(0); (x+0x1f) - y,2
	// Free memory pointer
	requires st'.MemSize() >= 0x80 //&& 0x80 <= st'.Read(0x40) <= 0xffff
	{
		var st := st';
		// ||0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x80,_,x,b=x,0x80,a,_,_,0x60,0xcc,_| // need to know more about x==b, i.e could it be == 0x20
		st := JumpDest(st);
		// ||0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x80,_,x,b,0x80,a,_,_,0x60,0xcc,_|
		st := Dup(st,4);
		// ||x,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||x,y,0x80,_,x,b,0x80,a,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		// ||0x00,x,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,x,y,0x80,_,x,b,0x80,a,_,_,0x60,0xcc,_|
		assert st.Peek(12) == 0xcc;
		assert st.Peek(3) == 0x80;
		assert st.Peek(7) == st'.Peek(5);
		st := Lt(st); // y < x
		// ||_,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||_,y,0x80,_,x,b,0x80,a,_,_,0x60,0xcc,_|
		st := IsZero(st);
		// ||_,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||_,y,0x80,_,x,b,0x80,a,_,_,0x60,0xcc,_|
		st := Push2(st,0x010c);
		// ||0x10c,_,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||0x10c,_,y,0x80,_,x,b,0x80,a,_,_,0x60,0xcc,_|
		assume {:axiom} st.IsJumpDest(0x10c);
		st := JumpI(st);
		if st.PC() == 0x10c { 
			// ||y,0x80,_,x,b,0x80,a,_,_,0x60,0xcc,_|
			assert st.Peek(4) <= 0xffff; // st'.Peek(3) == 
			assert st.Peek(6) <= (MAX_U256 as u256) - st'.Peek(4);
			st := block_0_0x010c(st); return st;
		
		} // if y >= x
		// ||0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,1);
		// ||0x00,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		assert st'.Peek(0) == st.Peek(1) && st'.Peek(3) == st.Peek(4) && st'.Peek(4) == st.Peek(5);		
		assert st.Peek(2) == st'.Peek(1);
		assert st.Peek(6) == st'.Peek(5);
		st := block_0_0x00fb(i,st); // i.e. y < x
		return st;
	}

	method block_0_0x00fb(i: nat, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00fb
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires (st'.Peek(0) == st'.Peek(1) && st'.Peek(2) == st'.Peek(6) == 0x80 && st'.Peek(10) == 0x60 && st'.Peek(11) == 0xcc)
	requires st'.Peek(4) == st'.Peek(5)
	requires var x := st'.Peek(5); var z := st'.Peek(7); z <= (MAX_U256 as u256) - x
	// Free memory pointer
	requires st'.MemSize() >= 0x80 //&& 0x80 <= st'.Read(0x40) <= 0xffff
	// Termination
	requires var y := st'.Peek(1); y as nat == i * 0x20
	requires var x := st'.Peek(4); var y := st'.Peek(1); y < x <= 0xffff
	decreases var x := st'.Peek(4); var y := st'.Peek(1); x-y,1
	{
		var st := st';
		// ||0x00,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,y,0x80,_,x,x,0x80,z,_,_,0x60,0xcc,_|
		st := Dup(st,3);
		// ||0x80,0x00,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||0x80,y,y,0x80,_,x,x,0x80,z,_,_,0x60,0xcc,_|
		assert st.Peek(0) == 0x80;
		assert st.Peek(1) == st'.Peek(1) <= 0xffff;
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0x80,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y+0x80,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := MLoad(st);
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||mem(y+0x80),y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		assert st'.Peek(1) == st.Peek(2) && st'.Peek(4) == st.Peek(5);
		assert st.Peek(3) == st.Peek(7) == 0x80;
		assert st.Peek(8) == st'.Peek(7);
		assert st.Peek(11) == 0x60;
		assert st.Peek(12) == 0xcc;
		// ||0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,mem(y+0x80),y,0x80,z,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,5);
		// ||_,0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||z,y,mem(y+0x80),y,0x80,z,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Add(st);
		assert {:split_here} true;
		assert st.Peek(3) == st.Peek(7) == 0x80;    
		// ||_,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||z+y,mem(y+0x80),y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		//var a := st'.Peek(0) as nat +0x80;
		//assert a>= 0x80;
		//assert st.Peek(1) == st.Read(st'.Peek(0) as nat +0x80);
		st := MStore(st);
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|

		//st.Read(mem(y+0x80))==z+y
		//assert st.Read(0x40) == st'.Read(0x40);
		//assert st.Read(st'.Peek(1) as nat) == 0x80;
		// assert 0x80 <= st.Read(0x40) <= 0xffff;
		
		st := Push1(st,0x20);
		// // ||0x20,y,0x80,_,x,x,0x80,_,_,_,0x60,0xcc,_|
		assert st.Peek(4) == st'.Peek(4) && st.Peek(5) == st'.Peek(5) ;
		assert st.Peek(7) == st'.Peek(7);
		assert (st.Peek(0) == 0x20 && st.Peek(2) == 0x80 && st.Peek(6) == 0x80 && st.Peek(10) == 0x60 && st.Peek(11) == 0xcc);
		assert st.Peek(7) <= (MAX_U256 as u256) - st.Peek(5);
		st := block_0_0x0104(i,st);
		return st;
	}

	method block_0_0x0104(i: nat, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0104
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(2) == 0x80 && st'.Peek(6) == 0x80 && st'.Peek(10) == 0x60 && st'.Peek(11) == 0xcc)
	requires st'.Peek(4) == st'.Peek(5)
	requires var x := st'.Peek(5); var y := st'.Peek(7); y <= (MAX_U256 as u256) - x
	// Free memory pointer
	requires st'.MemSize() >= 0x80 //&& 0x80 <= st'.Read(0x40) <= 0xffff
	
	// Termination
	requires var y := st'.Peek(1); y as nat == i * 0x20
	requires var x := st'.Peek(4); var y := st'.Peek(1); y < x <= 0xffff
	decreases var x := st'.Peek(4); var y := st'.Peek(1); x-y,0
	{
		var st := st';
		// ||0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||0x20,y,0x80,_,x,x,0x80,z,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		// ||0x00,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// Havoc 0
		// ||_,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		//||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// Havoc 0
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y+0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		assert st.Peek(0) >= st'.Peek(1);
		st := Swap(st,1);
		// ||0x00,_,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,y+0x20,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Pop(st);
		// ||y+0x20,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Push2(st,0x00f1);
		// ||0xf1,y+0x20,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		assume {:axiom} st.IsJumpDest(0xf1);
		st := Jump(st);
		// ||y+0x20,0x80,_,x,x,0x80,z,_,_,0x60,0xcc,_|
		assert st.Peek(3) == st.Peek(4);
		assert st.Peek(6) <= (MAX_U256 as u256) - st.Peek(4);
		st := block_0_0x00f1(i+1,st);
		return st;
	}

	method block_0_0x010c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x010c
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires (st'.Peek(1) == 0x80 && st'.Peek(5) == 0x80 && st'.Peek(9) == 0x60 && st'.Peek(10) == 0xcc)
	requires var a := st'.Peek(6); var b := st'.Peek(4); b <= 0xffff && a <= (MAX_U256 as u256) - b
	// Free memory pointer
	requires st'.MemSize() >= 0x80 //&& 0x80 <= st'.Read(0x40) <= 0xffff
	{
		var st := st';
		//||_,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		//||0x00,0x80,_,_,b,0x80,a,_,_,0x60,0xcc,_|
		st := JumpDest(st);
		//||_,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		//||0x00,0x80,_,_,b,0x80,a,_,_,0x60,0xcc,_|
		st := Pop(st);
		//||0x80,_,_,b,0x80,a,_,_,0x60,0xcc,_|
		st := Pop(st);
		//||_,_,b,0x80,a,_,_,0x60,0xcc,_|
		assert st.Operands() == 10;
		st := Pop(st);
		//||_,b,0x80,a,_,_,0x60,0xcc,_|
		st := Pop(st);
		//||b,0x80,a,_,_,0x60,0xcc,_|
		st := Swap(st,1);
		//||0x80,b,a,_,_,0x60,0xcc,_|
		st := Pop(st);
		//||b,a,_,_,0x60,0xcc,_|
		st := Swap(st,1);
		//||a,b,_,_,0x60,0xcc,_|
		st := block_0_0x0114(st);
		return st;
	}

	method block_0_0x0114(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0114
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(4) == 0x60 && st'.Peek(5) == 0xcc)
	requires var a := st'.Peek(0); var b := st'.Peek(1); b <= 0xffff && /*0x1f <= */ a <= (MAX_U256 as u256) - b // see below
	//requires var a := st'.Peek(0); var b := st'.Peek(1); b <= 0x20 && /*0x1f <= */ a <= (MAX_U256 as u256) - 0x20 // see below
	// Free memory pointer
	requires st'.MemSize() >= 0x80 //&& 0x80 <= st'.Read(0x40) <= 0xffff
	{
		var st := st';
		//||a,b,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		//||b,a,b,_,_,0x60,0xcc,_|
		assert st.Peek(0) == st'.Peek(1);
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//||b,a,b,_,_,0x60,0xcc,_|
		st := Add(st);
		//||a+b,b,_,_,0x60,0xcc,_|
		st := Swap(st,1);
		//||b,a+b,_,_,0x60,0xcc,_|
		st := Push1(st,0x1f);
		//||0x1f,b,a+b,_,_,0x60,0xcc,_|
		assert st.Peek(5) == 0x60 && st.Peek(6) == 0xcc;
		assert st.Peek(1) == st'.Peek(1) <= 0xffff;
		st := AndU5(st);
		//||0x1f&b,a+b,_,_,0x60,0xcc,_|
		//assert st.Peek(0) == st'.Peek(1);
		//assert st.Peek(1) == st'.Peek(0) + st'.Peek(1);
		assert st.Peek(0) <= 0x20;
		assert st.Peek(1) <= MAX_U256 as u256;
 		//assert st.Peek(1) - st.Peek(0) <= (MAX_U256 as u256 - 0x20);
		//assert st.Peek(0) <= st.Peek(1);
		st := Dup(st,1);
		//||0x1f&b,0x1f&b,a+b,_,_,0x60,0xcc,_|
		assert st.Peek(5) == 0x60 && st.Peek(6) == 0xcc;
		st := IsZero(st);
		assert st.Peek(0) == 0 ==> st.Peek(1) != 0;
		assert st.Peek(0) == 1 ==> st.Peek(1) == 0;
		
		//||1,0x1f&b==0,a+b,_,_,0x60,0xcc,_|
		//||0,0x1f&b!=0,a+b,_,_,0x60,0xcc,_|
		st := Push2(st,0x0139);
		//||0x0139,1,0x1f&b==0,a+b,_,_,0x60,0xcc,_|
		//||0x0139,0,0x1f&b!=0,a+b,_,_,0x60,0xcc,_|
		//assert st.Peek(2) == st'.Peek(1);
		assert st.Peek(0) == 0x0139  && st.Peek(6) == 0x60;
		assert st.Peek(2) <= 0x20;
		assert st.Peek(3) <= MAX_U256 as u256; // ! need more bounds 
		assert st.Peek(3) - st.Peek(2) <= (MAX_U256 as u256 - 0x20);
		//st := block_0_0x011f(st);
		return st;
	}

	method block_0_0x011f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x011f
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(0) == 0x139 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	requires st'.Peek(1) == 0 ==> st'.Peek(2) != 0
	requires st'.Peek(1) == 1 ==> st'.Peek(2) == 0
	requires st'.Peek(2) <= st'.Peek(3) && st'.Peek(2) <= 0x20
	requires st'.Peek(3) - st'.Peek(2) <= (MAX_U256 as u256 - 0x20)
	// Free memory pointer
	requires st'.MemSize() >= 0x80 //&& 0x80 <= st'.Read(0x40) <= 0xffff
	{
		var st := st';
		//||0x0139,1,0x1f&b==0,a+b,_,_,0x60,0xcc,_|
		//||0x0139,0,0x1f&b!=0,a+b,_,_,0x60,0xcc,_|
		assume {:axiom} st.IsJumpDest(0x139);
		st := JumpI(st);
		if st.PC() == 0x139 { 
			assert st'.Peek(1) != 0;
			st := block_0_0x0139(st); 
			return st;
		} // cond was true
		assert st'.Peek(1) == 0;
		assert st.Peek(0) == st'.Peek(2) != 0;
		//||0x1f&b!=0,a+b,_,_,0x60,0xcc,_|
		st := Dup(st,1);
		//||0x1f&b!=0,0x1f+b!=0,a+b,_,_,0x60,0xcc,_|
		st := Dup(st,3);
		//||a+b,0x1f&b!=0,0x1f&b!=0,a+b,_,_,0x60,0xcc,_|
		assert st.Peek(1) <= st.Peek(0); 
		st := Sub(st);
		//||(a+b)-(0x1f&b),0<b<=0xffff,_,_,_,0x60,0xcc,_| i.e. (a+b)-(0x1f&b) == a since b < 0xffff
		st := Dup(st,1);
		//||a,a,*,_,_,_,0x60,0xcc,_|
		st := MLoad(st);
		//||mem(a),a,*,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x01);
		//||0x01,mem(a),a,*,_,_,_,0x60,0xcc,_|
		st := Dup(st,4);
		//||*,0x01,mem(a),a,*,_,_,_,0x60,0xcc,_|
		assert st.Peek(3) <= (MAX_U256 as u256 - 0x20); //(MAX_U256 as u256 - 0xffff);
		st := block_0_0x0128(st);
		return st;
	}

	method block_0_0x0128(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0128
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(1) == 0x1 && st'.Peek(8) == 0x60 && st'.Peek(9) == 0xcc)
	requires st'.Peek(0) <= 0x20
	requires st'.Peek(3) <= (MAX_U256 as u256 - 0x20)//(MAX_U256 as u256 - 0xffff)
	// Free memory pointer
	requires st'.MemSize() >= 0x80 //&& 0x80 <= st'.Read(0x40) <= 0xffff
	{
		var st := st';
		//||*,0x01,#,^,_,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		assert st.Peek(1) <= st.Peek(0);
		//||0x20,*,0x01,#,^,_,_,_,_,0x60,0xcc,_|
		st := Sub(st);
		assert {:split_here} true;
		//||0x20-*,0x01,#,^,_,_,_,_,0x60,0xcc,_|
		assert (st.Peek(8) == 0x60 && st.Peek(9) == 0xcc);
		assert st'.Peek(3) == st.Peek(3);
		assert 0 <= st.Peek(0);
		st := Push2(st,0x0100);
		//assert {:split_here} true;
		//||0x100,0x20-*,0x01,#,^,_,_,_,_,0x60,0xcc,_|
		assert st.Peek(0) == 0x100 && 0 <= st.Peek(1) <= 0x20;
		var e := MathUtils.Pow(st.Peek(0) as nat,st.Peek(1) as nat);
		assume 1 <= e <= 0x2000;
		st := Exp(st);
		//||e,0x01,#,^,_,_,_,_,0x60,0xcc,_|
		assert st.Peek(0) == e as u256;
		assert st.Peek(1) <= st.Peek(0);
		
		st := Sub(st);
		assert {:split_here} true;
		assert st'.Peek(3) == st.Peek(2);
		assert (st.Peek(7) == 0x60 && st.Peek(8) == 0xcc);
		//||e-1,#,^,_,_,_,_,0x60,0xcc,_|
		st := Not(st);
		//||!(e-1),#,^,_,_,_,_,0x60,0xcc,_|
		st := And(st);
		//||#&!(e-1),^,_,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		//||^,#&!(e-1),^,_,_,_,_,0x60,0xcc,_|
		//assert {:split_here} true;
		assert st'.Peek(3) == st.Peek(2) <= (MAX_U256 as u256 - 0x20); //(MAX_U256 as u256 - 0xffff);
		assert (st.Peek(7) == 0x60 && st.Peek(8) == 0xcc);
		//assert st.Read(0x40) <= st.Peek(1) ;
		st := block_0_0x0133(st);
		return st;
	}

	method block_0_0x0133(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0133
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires (st'.Peek(7) == 0x60 && st'.Peek(8) == 0xcc)
	requires st'.Peek(2) <= (MAX_U256 as u256 - 0x20) //(MAX_U256 as u256 - 0xffff) // 
	// Free memory pointer
	requires st'.MemSize() >= 0x80 //&& 0x80 <= st'.Read(0x40) <= 0xffff
	//requires st'.Read(0x40) <= st'.Peek(1) 
	{
		var st := st';
		//||_,_,!#,_,_,_,_,0x60,0xcc,_|
		st := MStore(st);
		//||!#,_,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		//||0x20,!#,_,_,_,_,0x60,0xcc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||$,_,_,_,_,0x60,0xcc,_|
		st := Swap(st,2);
		//||_,_,$,_,_,0x60,0xcc,_|
		st := Pop(st);
		//||_,$,_,_,0x60,0xcc,_|
		st := block_0_0x0139(st);
		return st;
	}

	method block_0_0x0139(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0139
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(4) == 0x60 && st'.Peek(5) == 0xcc)
	// Free memory pointer
	requires st'.MemSize() >= 0x80
	//requires st'.Read(0x40) <= st'.Peek(1) 
	{
		var st := st';
		//||_,$,_,_,0x60,0xcc,_|
		st := JumpDest(st);
		//||_,$,_,_,0x60,0xcc,_|
		st := Pop(st);
		//||$,_,_,0x60,0xcc,_|
		st := Swap(st,3);
		//||0x60,_,_,$,0xcc,_|
		st := Pop(st);
		//||_,_,$,0xcc,_|
		st := Pop(st);
		//||_,$,0xcc,_|
		st := Pop(st);
		//||$,0xcc,_|
		st := Push1(st,0x40);
		//||0x40,$,0xcc,_|
		st := MLoad(st);
		//||mem(0x40),$,0xcc,_|
		//assert st.Peek(0)== st.Read(0x40) <= st.Peek(1);
		st := block_0_0x0142(st);
		return st;
	}

	method block_0_0x0142(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0142
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0xcc)
	// Free memory pointer
	requires st'.MemSize() >= 0x80
	//requires var x := st'.Peek(0); x == st'.Read(0x40) <= st'.Peek(1) // TRY TO GET BOUND FOR PEEK1
	{
		var st := st';
		//||^,@,0xcc,_|
		st := Dup(st,1);
		//||^,^,@,0xcc,_|
		st := Swap(st,2);
		//||@,^,^,0xcc,_|
		assume st.Peek(1) <= st.Peek(0); // ^ <= @ need to track memory
		st := Sub(st);
		//||_,_,0xcc,_|
		st := Swap(st,1);
		//||_,_,0xcc,_|
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
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		//|fp=0x0060|0xcc,_|
		st := JumpDest(st);
		//|fp=0x0060|0xcc,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0xcc,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,0xcc,_|
		st := SLoad(st);
		//|fp=0x0060|0x1a,0x00,0xcc,_|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,0x1a,0x00,0xcc,_|
		st := Dup(st,2);
		//|fp=0x0060|0x1a,0x01,0x1a,0x00,0xcc,_|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,0x1a,0x01,0x1a,0x00,0xcc,_|
		st := AndU1(st);
		//|fp=0x0060|0,0x01,0x1a,0x00,0xcc,_|
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
	requires st'.Peek(0) == 0
	requires st'.Peek(2) == st'.Load(0x00)
	requires (st'.Peek(1) == 0x1 && st'.Peek(3) == 0x0 && st'.Peek(4) == 0xcc)
	// Storate Items
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		//|fp=0x0060|0,0x01,Load(0),0x00,0xcc,_|
		st := IsZero(st);
		//|fp=0x0060|1,0x01,Load(0),0x00,0xcc,_|
		st := Push2(st,0x0100);
		//|fp=0x0060|0x100,1,0x01,Load(0),0x00,0xcc,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		//|fp=0x0060|0x100,0x01,Load(0),0x00,0xcc,_|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|0xff,Load(0),0x00,0xcc,_|
		assert st.Peek(2) == 0x00 && st.Peek(3) == 0xcc;
		// ==========================================================
		// NOTE: Reimplemented following to avoid need to reason about bitvector
		// arithmetic.
		// st := And(st);
		if st.Peek(0) == MAX_U256 as u256 { 
			// Masking against MAX_U256 (a nop)
			st := st.Pop().Next();
		} else {
			// Masking against 0xFF
			st := AndU8(st);
		}
		// ==========================================================
		// |fp=0x0060|Load(0)=0x1a,0x00,0xcc,_|
		st := Push1(st,0x02);
		// |fp=0x0060|0x02,Load(0)=0x1a,0x00,0xcc,_|
		st := Swap(st,1);
		// |fp=0x0060|Load(0)=0x1a,0x02,0x00,0xcc,_|
		st := Div(st);
		// |fp=0x0060|len=0xd,0x00,0xcc,_|
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
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.	
	{
		var st := st';
		// |fp=0x0060|len=0xd,0x00,0xcc,_|
		st := Dup(st,1);
		// |fp=0x0060|len,len,0x00,0xcc,_|
		st := Push1(st,0x1f);
		// |fp=0x0060|0x1f,len,len,0x00,0xcc,_|
		st := Add(st);
		// |fp=0x0060|len+0x1f,len,0x00,0xcc,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,len+0x1f,len,0x00,0xcc,_|
		assert st.Peek(0) == 0x20 && st.Peek(3) == 0x00 && st.Peek(4) == 0xcc;
		st := Dup(st,1);
		// |fp=0x0060|0x20,0x20,len+0x1f,len,0x00,0xcc,_|
		st := Swap(st,2);
		// |fp=0x0060|len+0x1f,0x20,0x20,len,0x00,0xcc,_|
		st := Div(st);
		var n := st.Peek(0) as nat;
		// |fp=0x0060|n,0x20,len,0x00,0xcc,_|
		st := Mul(st);
		// |fp=0x0060|n*0x20,len,0x20,_,0x00,0xcc,_| // n is len rounded up
    	assert st.Peek(1) == st'.Peek(0) == 13;
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
	// Static stack items
	requires (st'.Peek(0) < 0xff7f)
	requires (st'.Peek(1) < 0xffff)
	requires (st'.Peek(2) == 0x0 && st'.Peek(3) == 0xcc)
	// Storage
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.	
	{
		var st := st';
		// |fp=0x0060|x,m,0x00,0xcc,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,x,m,0x00,0xcc,_|
		st := Add(st);
		// |fp=0x0060|x+0x20,m,0x00,0xcc,_|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,x+0x20,m,0x00,0xcc,_|
		st := MLoad(st);
		// |fp=0x0060|0x60,x+0x20,m,0x00,0xcc,_|
		st := Swap(st,1);
		// |fp=0x0060|x+0x20,0x60,m,0x00,0xcc,_|
		st := Dup(st,2);
		// |fp=0x0060|0x60,x+0x20,0x60,m,0x00,0xcc,_|
		st := Add(st);
		// |fp=0x0060|x+0x80,0x60,m,0x00,0xcc,_|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,x+0x80,0x60,m,0x00,0xcc,_|
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
	requires 0x80 <= st'.Peek(1) < 0xffff
	requires st'.Peek(3) < 0xffff
	requires (st'.Peek(0) == 0x40 && st'.Peek(2) == 0x60 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0xcc)
	// Storage
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.	
	{
		var st := st';
		// |fp=0x0060|0x40,x+0x80,0x60,m,0x00,0xcc,_|
		st := MStore(st);
		// ||0x60,m,0x00,0xcc,_|
		st := Dup(st,1);
		// ||0x60,0x60,m,0x00,0xcc,_|
		st := Swap(st,3);
		// ||0x00,0x60,m,0x60,0xcc,_|
		st := Swap(st,2);
		// ||x,0x60,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||0x60,m,0x00,0x60,0xcc,_|
		st := Dup(st,2);
		// ||x,0x60,m,0x00,0x60,0xcc,_|
		st := Dup(st,2);
		// ||0x60,m,0x60,m,0x00,0x60,0xcc,_|
		st := MStore(st);		
		// ||0x60,m,0x00,0x60,0xcc,_|
		st := block_0_0x0510(st);
		return st;
	}

	method block_0_0x0510(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0510
	/// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x60 && st'.Peek(4) == 0xcc)
	// Storage
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.	
	{
		var st := st';
		// ||0x60,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,0x60,_,0x00,0x60,0xcc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,3);
		// ||0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,1);
		// ||0x00,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := SLoad(st);
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x01);
		// ||0x01,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,2);
		// ||_,0x01,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x01);
		st := block_0_0x051b(st);
		return st;
	}

	method block_0_0x051b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x051b
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(0) == 0x1 && st'.Peek(2) == 0x1 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0x80 && st'.Peek(7) == 0x0 && st'.Peek(8) == 0x60 && st'.Peek(9) == 0xcc)
	requires (st'.Peek(3) == st'.Load(0))
	requires (st'.Peek(1) % 2 == 0)
	// Storage
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.
	{
		var st := st';
		// ||0x01,_,0x01,2*l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := AndU1(st);
		// ||firstBit P'(1),0x01,2*l,0x00,0x80,_,0x00,0x60,0xcc,_|
		//assert st.Peek(0) == 0;
		st := IsZero(st);
		// ||1 or 0,0x01,2*l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0100);
		// ||0x100,1 or 0,0x01,2*l,0x00,0x80,_,0x00,0x60,0xcc,_|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		// ||{0,x100},0x01,2*l,0x00,0x80,_,0x00,0x60,0xcc,_|
    	assert st.Peek(4) == 0x80 && st.Peek(6) == 0x00 && st.Peek(7) == 0x60 && st.Peek(8) == 0xcc;
		assert st.Peek(1) <= st.Peek(0); // requires peek 0 to be 0x100, not 0
		//||_,0x01,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Sub(st);
		assert st.Peek(0) in {MAX_U256 as u256, 0xFF};
		// ||{mx256,xff},2*l,0x00,0x80,_,0x00,0x60,0xcc,_|
		// ==========================================================
		// NOTE: Reimplemented following to avoid need to reason about bitvector
		// arithmetic.
		// st := And(st);
		if st.Peek(0) == MAX_U256 as u256 { 
			// Masking against MAX_U256 (a nop)
			st := st.Pop().Next();
		} else {
			// Masking against 0xFF
			st := AndU8(st);
		}
		// ==========================================================
		// ||2*l,0x00,0x80,_,0x00,0x60,0xcc,_|
		
		st := Push1(st,0x02);
		//||0x02,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||2*l,0x02,0x00,0x80,_,0x00,0x60,0xcc,_|		
		st := block_0_0x0526(st);
		return st;
	}

	method block_0_0x0526(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0526
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(1) == 0x2 && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 && st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	requires (st'.Peek(0) == st'.Load(0))
	// Storage
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.	
	{
		var st := st';
		// ||2*l,0x02,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Div(st);
		var l := st.Peek(0);
		assert l == 13;		
		// ||l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,1);
		// ||l,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := IsZero(st);
		// ||l,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0573);
		// ||0x573,_,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		assert (st.Peek(3) == 0x0 && st.Peek(4) == 0x80 && st.Peek(6) == 0x0 && st.Peek(7) == 0x60 && st.Peek(8) == 0xcc);
		assume {:axiom} st.IsJumpDest(0x573);
		st := JumpI(st);
		if st.PC() == 0x573 { st := block_0_0x0573(st); return st;} // l == 0
		// ||l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,1);
		// ||l,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x1f);
		// ||0x1f,l,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Lt(st);
		assert (st.Peek(2) == 0x0 && st.Peek(3) == 0x80 && st.Peek(6) == 0x60 && st.Peek(7) == 0xcc);
		st := block_0_0x0531(st);
		return st;
	}

	method block_0_0x0531(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0531
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)	
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(0) in {0,1}) && (st'.Peek(0) == 1 <==> 0x1f < st'.Peek(1))
	requires (st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 && st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	requires (st'.Peek(1) == 13)
	// Storage
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.	
	{
		var st := st';
		// ||_,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0548);
		// ||0x548,_,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		assume {:axiom} st.IsJumpDest(0x548);
		st := JumpI(st);
		if st.PC() == 0x548 { 
			// l >= 0x1f
			//
			// Deadcode begins here.  The reason is that the following code is used
			// to account for copying strings whose length exceeds 31 bytes.
			// However, the actual length of the string involved in this case
			// ("Wrapped Ether") is only 13 bytes.
			assert false;
			st := block_0_0x0548(st); return st;
		} 
		// ||l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0100);
		// ||0x100,l,0x00,0x80,_,0x00,0x60,0xcc,_|
    	assert st.Peek(7) == st'.Peek(7) == 0xcc;    
		assert st.Peek(1) == 13 && st.Peek(2) == 0x00 && st.Peek(3) == 0x80 && st.Peek(5) == 0x0 && st.Peek(6) == 0x60 && st.Peek(7) == 0xcc;
		st := Dup(st,1);
		// ||0x100,0x100,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,4);
		// ||0x00,0x100,0x100,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := SLoad(st);
    	assert st.Peek(9) == st'.Peek(7) == 0xcc;    
		// ||_,0x100,0x100,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Div(st);
		// ||_,0x100,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Mul(st);
		// ||_,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := block_0_0x053d(st);
		return st;
	}

	method block_0_0x053d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x053d
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)	
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 && st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	requires (st'.Peek(1) == 13)
	{
		var st := st';
		// ||_,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,4);
		// ||0x80,_,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := MStore(st);
		// ||l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Swap(st,2);
		// ||0x80,0x00,l,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,0x80,0x00,l,_,0x00,0x60,0xcc,_|
		st := Add(st);
		// ||0xa0,0x00,l,_,0x00,0x60,0xcc,_|
		st := Swap(st,2);
		// ||l,0x00,0xa0,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0573);
		// ||0x573,l,0x00,0xa0,_,0x00,0x60,0xcc,_|
		assume {:axiom} st.IsJumpDest(0x573);
		st := Jump(st);
		// ||l,0x00,0xa0,_,0x00,0x60,0xcc,_|
		st := block_0_0x0573(st);
		return st;
	}

	method block_0_0x0548(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0548
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)	
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(1) == 0x0 && st'.Peek(2) == 0x80 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	requires (st'.Peek(0) == 13)
	{
		var st := st';
		// ||l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := JumpDest(st);
		// ||l,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,3);
		// ||0x80,l,0x00,0x80,_,0x00,0x60,0xcc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||n,0x00,0x80,_,0x00,0x60,0xcc,_|
		var n := st.Peek(0);
		assert 0x80 <= n && n < 0xffff;
		st := Swap(st,2);
		//assert {:split_here} true;
		// ||0x80,0x00,n,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||0x00,0x80,n,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x00);
		// ||0x00,0x00,0x80,n,_,0x00,0x60,0xcc,_|
		assert st.Peek(7) == 0xcc;
		assert {:split_here} true;
		st := MStore(st);
		assert st.Read(0x00) == 0x00;
		// ||0x80,n,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,0x80,n,_,0x00,0x60,0xcc,_|
		assert (st.Peek(0) == 0x20 && st.Peek(1) == 0x80 && st.Peek(4) == 0x0 && st.Peek(5) == 0x60 && st.Peek(6) == 0xcc);
		st := block_0_0x0552(n,st);
		return st;
	}

	method block_0_0x0552(n: u256,st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0552
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff && st'.Read(0x00) == 0x00
	requires (st'.Read(0x60) <= 0xffff)	
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x80 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	requires (0x80 <= st'.Peek(2) == n < 0xffff)
	{
		var st := st';
		// ||0x20,0x80,n,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x00);
		// ||0x00,0x20,0x80,n,_,0x00,0x60,0xcc,_|
		st := Keccak256(st); // sha3(st'.Read(0x00))
		// ||k,0x80,n,_,0x00,0x60,0xcc,_|
		//assert st.Peek(0) == sha3 of 0x00 ???, ie the value in st'.Read(0x00));
		//assume st.Peek(0) <= (MAX_U256 as u256 - 2);
		st := Swap(st,1);
		// ||0x80,k,n,_,0x00,0x60,0xcc,_|
		st := block_0_0x0556(0x80,n,st);
		return st;
	}

	method block_0_0x0556(i: u256, n: u256,st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0556
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)	
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	requires (st'.Peek(0) == i && st'.Peek(2) == n)
	//requires st'.Peek(1) <= (MAX_U256 as u256 - 2)
	// Termination
	requires 0x80 <= i <= n < 0xffff
	decreases n-i,2
	{
		var st := st';
		// ||0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||i,k,n,_,0x00,0x60,0xcc,_|
		st := JumpDest(st);
		// ||0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||i,k,n,_,0x00,0x60,0xcc,_|
		st := Dup(st,2);
		// ||_,0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||k,i,k,n,_,0x00,0x60,0xcc,_|
		st := SLoad(st);
		// ||_,0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||_,i,k,n,_,0x00,0x60,0xcc,_|
		assert {:split_here} true;
		st := Dup(st,2);
		// ||0x80,_,0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||i,_,i,k,n,_,0x00,0x60,0xcc,_|
		st := MStore(st);
		assert {:split_here} true;
		//assert st.Read(0x40) == st'.Read(0x40);
		// ||0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||i,k,n,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||_,0x80,_,_,0x00,0x60,0xcc,_|
		// ||k,i,n,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x01);
		// ||0x01,_,0x80,_,_,0x00,0x60,0xcc,_|
		// ||0x01,k,i,n,_,0x00,0x60,0xcc,_|
		//assert st'.Peek(1) == st.Peek(1) <= (MAX_U256 as u256 - 2);
		//assume (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256); // k + 1 is never used and therefore doesn't matter if it overflows
		//assert st.Peek(0) == 1;
		st := Add(st);
		// ||k+1,i,n,_,0x00,0x60,0xcc,_|
		//assert st.Peek(0) == st'.Peek(1) + 1 <= (MAX_U256 as u256 - 1);
		st := block_0_0x055f(i,n,st);
		return st;
	}

	method block_0_0x055f(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x055f
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	requires (st'.Peek(1) == i && st'.Peek(2) == n)
	//requires st'.Peek(0) <= (MAX_U256 as u256 - 1)
	// Termination
	requires 0x80 <= i <= n < 0xffff
	decreases n-i,1
	{
		var st := st';
		// ||_,0x80,_,_,0x00,0x60,0xcc,_|
		// ||k+1,i,n,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||i,k+1,n,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||0x20,i,k+1,n,_,0x00,0x60,0xcc,_|
    	assert st.Peek(7) == st'.Peek(6) == 0xcc;
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||i+0x20,k+1,n,_,0x00,0x60,0xcc,_|
		st := Dup(st,1);
		// ||i+0x20,i+0x20,k+1,n,_,0x00,0x60,0xcc,_|
		st := Dup(st,4);
		// ||n,i+0x20,i+0x20,k+1,n,_,0x00,0x60,0xcc,_|
		st := Gt(st);
		// ||1 if n > i+0x20 else 0,i+0x20,k+1,n,_,0x00,0x60,0xcc,_|
		//assert st.Peek(2) <= (MAX_U256 as u256 - 1);
		st := block_0_0x0566(i+0x20,n,st);
		return st;
	}

	method block_0_0x0566(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0566
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	requires (st'.Peek(0) in {0,1}) && (st'.Peek(0) == 0 <==> n <= i)
	requires (st'.Peek(1) == i && st'.Peek(3) == n)
	//requires st'.Peek(2) <= (MAX_U256 as u256 - 1)
	// Termination
	requires n < 0xffff && 0xA0 <= i <= (n+0x20)
	decreases n+0x20-i,0
	{
		var st := st';
		// ||cond,i,k+1,n,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0556);
		// ||0x556,cond,i,k+1,n,_,0x00,0x60,0xcc,_|
		assume {:axiom} st.IsJumpDest(0x556);
		st := JumpI(st);
		if st.PC() == 0x556 { 
			// ||i,k+1,n,_,0x00,0x60,0xcc,_|
			//assert st.Peek(1) <= (MAX_U256 as u256 - 1);
			//assert st'.Peek(0) == 1; // probably don't need these, leaving for tidy up, i.e. n > i+0x20
			st := block_0_0x0556(i,n,st); 
			return st; 
			}
		//assert st'.Peek(0) == 0;
		// ||i,k+1,n,_,0x00,0x60,0xcc,_|
		st := Dup(st,3);
		// ||n,i,k+1,n,_,0x00,0x60,0xcc,_|
		assert (st.Peek(5) == 0x0 && st.Peek(6) == 0x60 && st.Peek(7) == 0xcc);
		st := Swap(st,1);
		assert st.Peek(5) == 0x00;
		//||i,n,k+1,n,_,0x00,0x60,0xcc,_|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//||n-i,k+1,n,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x1f);
		//||0x1f,n-i,k+1,n,_,0x00,0x60,0xcc,_|
		st := AndU5(st);
		//||first 5 bits of n-i,k+1,n,_,0x00,0x60,0xcc,_|
		st := Dup(st,3);
		// ||n,first 5 bits of n-i,k+1,n,_,0x00,0x60,0xcc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := block_0_0x0571(st);
		return st;
	}

	method block_0_0x0571(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0571
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	requires (st'.Peek(0) as nat + st'.Peek(1) as nat) <= (MAX_U256)
	{
		var st := st';
		// ||n,first 5 bits of n-i,k+1,n,_,0x00,0x60,0xcc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||n+first bits,k+1,n,_,0x00,0x60,0xcc,_|
		st := Swap(st,2);
		// ||_,0x00,0xa0,_,0x00,0x60,0xcc,_|
		// ||n,k+1,n+first bits,_,0x00,0x60,0xcc,_|
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := block_0_0x0573(st);
		return st;
	}

	method block_0_0x0573(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0573
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		//||_,0x00,0xa0,_,0x00,0x60,0xcc,_|
		// ||n,k+1,n+first bits,_,0x00,0x60,0xcc,_|
		//||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := JumpDest(st);
		//||_,0x00,0xa0,_,0x00,0x60,0xcc,_|
		// ||n,k+1,n+first bits,_,0x00,0x60,0xcc,_|
		//||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Pop(st);
		//||0x00,0xa0,_,0x00,0x60,0xcc,_|
		// ||k+1,n+first bits,_,0x00,0x60,0xcc,_|
		//||0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Pop(st);
		//||0xa0,_,0x00,0x60,0xcc,_|
		// ||n+first bits,_,0x00,0x60,0xcc,_|
		//||0x80,_,0x00,0x60,0xcc,_|
		st := Pop(st);
		// ||_,0x00,0x60,0xcc,_|
		st := Pop(st);
		//||0x00,0x60,0xcc,_|
		st := Pop(st);
		//||0x60,0xcc,_|
		st := Dup(st,2);
		//||0xcc,0x60,0xcc,_|
		assume {:axiom} st.IsJumpDest(0xcc);
		st := Jump(st);
		st := block_0_0x00cc(st);
		return st;
	}

}
