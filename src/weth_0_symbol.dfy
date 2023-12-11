
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
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
  // Termination
  requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.        
	{
		var st := st';
		// |fp=0x0060|_|
		st := JumpDest(st);
		// |fp=0x0060|_|
		st := CallValue(st);
		// |fp=0x0060|_,_|
		st := IsZero(st);
		// |fp=0x0060|_,_|
		st := Push2(st,0x02ed);
		// |fp=0x0060|0x2ed,_,_|
		assume st.IsJumpDest(0x2ed);
		st := JumpI(st);
		if st.PC() == 0x2ed { st := block_0_0x02ed(st); return st;}
		// |fp=0x0060|_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,_|
		st := Dup(st,1);
		// |fp=0x0060|0x00,0x00,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x02ed(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02ed
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
  // Termination
  requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.        
	{
		var st := st';
		// |fp=0x0060|_|
		st := JumpDest(st);
		// |fp=0x0060|_|
		st := Push2(st,0x02f5);
		// |fp=0x0060|0x2f5,_|
		st := Push2(st,0x0b30);
		// |fp=0x0060|0xb30,0x2f5,_|
		assume st.IsJumpDest(0xb30);
		st := Jump(st);
		st := block_0_0x0b30(st);
		return st;
	}

	method block_0_0x02f5(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02f5
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff      
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(1) == 0x2f5)
	// Termination	
  requires st'.Read(0x60) <= 0xffff    
	{
		var st := st';
		// ||0x60,0x2f5,_|
		st := JumpDest(st);
		// ||0x60,0x2f5,_|
		st := Push1(st,0x40);
		// ||0x40,0x60,0x2f5,_|
		st := MLoad(st);
		// ||?n,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||?n,?n,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||?n,?n,?n,0x60,0x2f5,_|
		st := Push1(st,0x20);
		// ||0x20,?n,?n,?n,0x60,0x2f5,_|
		st := Add(st);
		// ||?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Dup(st,3);
		// ||?n,?n+0x20,?n,?n,0x60,0x2f5,_|    
		st := block_0_0x02ff(st);
		return st;
	}

	method block_0_0x02ff(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02ff
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff    
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(4) == 0x60 && st'.Peek(5) == 0x2f5)
	// Termination	
	requires var p := st'.Peek(2); p >= 0x80 // && st'.Peek(1) == p + 0x20
	requires var q := st'.Peek(1); q >= 0x80  
  requires st'.Read(0x60) <= 0xffff  
	{
		var st := st';
		// ||?n,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||?n+0x20,?n,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Sub(st);
		// ||0x20,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Dup(st,3);
		// ||?n,0x20,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := MStore(st);    
		// ||?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Dup(st,4);
		// ||0x60,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||?n+0x20,0x60,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||0x60,?n+0x20,0x60,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := MLoad(st);
		// ||_,?n+0x20,0x60,?n+0x20,?n,?n,0x60,0x2f5,_|    
		st := block_0_0x0307(st);
		return st;
	}

	method block_0_0x0307(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0307
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff    
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x60 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
	// Termination	
	requires var p := st'.Peek(1); p >= 0x80
  requires st'.Read(0x60) <= 0xffff
	{
		var st := st';
		// ||_,?n+0x20,0x60,?n+0x20,?n,?n,0x60,0x2f5,_|        
		st := Dup(st,2);
		// ||?n+0x20,_,?n+0x20,0x60,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := MStore(st);
		// ||?n+0x20,0x60,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Push1(st,0x20);
		// ||0x20,?n+0x20,0x60,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Add(st);
		// ||?n+0x40,0x60,?n+0x20,?n,?n,0x60,0x2f5,_|
		st := Swap(st,2);
		// ||?n+0x20,0x60,?n+0x40,?n,?n,0x60,0x2f5,_|
		st := Pop(st);
		// ||0x60,?n+0x40,?n,?n,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||0x60,0x60,?n+0x40,?n,?n,0x60,0x2f5,_|
		st := MLoad(st);
		st := block_0_0x0310(st);
		return st;
	}

	method block_0_0x0310(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0310
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff  
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(1) == 0x60 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
  requires var x := st'.Peek(0); x == st'.Read(0x60) <= 0xffff
	{
		var st := st';
		// ||_,0x60,_,?n,_,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||0x60,_,?n,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		// ||0x20,0x60,_,?n,_,_,0x60,0x2f5,_|
		st := Add(st);
		// ||0x80,_,?n,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||_,0x80,_,?n,_,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||_,_,0x80,_,?n,_,0x60,0x2f5,_|
		st := Dup(st,4);
		// ||_,_,_,0x80,_,?n,_,0x60,0x2f5,_|
		st := Dup(st,4);
		// ||0x80,_,?n,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x00);
		st := block_0_0x031a(0,st); 
		return st;
	}

	method block_0_0x031a(i:nat, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x031a
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires (st'.Peek(1) == 0x80 && st'.Peek(5) == 0x80 && st'.Peek(9) == 0x60 && st'.Peek(10) == 0x2f5)
  // Termination
  requires var y := st'.Peek(0); y as nat == 0x20 * i
  requires var x := st'.Peek(3); x <= 0xffff
 	requires var x := st'.Peek(3); var y := st'.Peek(0); y <= (x+0x1f)
	decreases var x := st'.Peek(3); var y := st'.Peek(0); (x+0x1f) - y,2
  {
		var st := st';
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||?1,0x80,_,?2,_,0x80,_,_,_,0x60,0x2f5,_|
		st := JumpDest(st);
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||?1,0x80,_,?2,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,4);
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||?2,?1,0x80,_,?2,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||?1,?2,?1,0x80,_,?2,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Lt(st);
    assert st.Peek(2) == 0x80;
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,?1,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := IsZero(st);
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,?1,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Push2(st,0x0335);
		// ||0x335,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||0x335,_,?1,0x80,_,2?,_,0x80,_,_,_,0x60,0x2f5,_|
		assume st.IsJumpDest(0x335);
		st := JumpI(st);
		if st.PC() == 0x335 { st := block_0_0x0335(st); return st;} // exit is ?1 >= ?2
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||?1,0x80,_,?2,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
    assert st.Peek(0) == st.Peek(1) == st'.Peek(0) && st.Peek(4) == st'.Peek(3);
		st := block_0_0x0324(i,st);
		return st;
	}

	method block_0_0x0324(i:nat, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0324
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires (st'.Peek(2) == 0x80 && st'.Peek(6) == 0x80 && st'.Peek(10) == 0x60 && st'.Peek(11) == 0x2f5)
 	// Termination
	requires var y := st'.Peek(1); y as nat == i * 0x20
	requires var x := st'.Peek(4); var y := st'.Peek(1); y < x <= 0xffff
	decreases var x := st'.Peek(4); var y := st'.Peek(1); x-y,1
	{
		var st := st';
		// ||0x00,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||?1,?1,0x80,_,?2,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,3);
		// ||0x80,0x00,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||0x80,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		// ||0x80,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := MLoad(st);
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
    assert st.Peek(3) == st.Peek(7) == 0x80 && st.Peek(11) == 0x60 && st.Peek(12) == 0x2f5;
    assert st.Peek(2) <= st.Peek(5);
		// ||0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,5);
		// ||_,0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,_,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		// ||_,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
    assert st.Peek(3) == st.Peek(7) == 0x80;    
		st := MStore(st);
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||?1,0x80,_,?2,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		st := block_0_0x032d(i,st);
		return st;
	}

	method block_0_0x032d(i:nat, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x032d
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(2) == 0x80 && st'.Peek(6) == 0x80 && st'.Peek(10) == 0x60 && st'.Peek(11) == 0x2f5)
	// Termination
	requires var y := st'.Peek(1); y as nat == i * 0x20
	requires var x := st'.Peek(4); var y := st'.Peek(1); y < x <= 0xffff
	decreases var x := st'.Peek(4); var y := st'.Peek(1); x-y,0
	{
		var st := st';
		// ||0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||0x20,?x,0x80,_,?y,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||0x00,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||?x,0x20,?x,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// Havoc 0
		// ||_,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,0x20,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// Havoc 0
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||0x00,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||_,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		// ||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Push2(st,0x031a);
		// ||0x31a,_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		assume st.IsJumpDest(0x31a);
		st := Jump(st);
		st := block_0_0x031a(i+1,st);
		return st;
	}

	method block_0_0x0335(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0335
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires (st'.Peek(1) == 0x80 && st'.Peek(5) == 0x80 && st'.Peek(9) == 0x60 && st'.Peek(10) == 0x2f5)
	{
		var st := st';
		// ||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := JumpDest(st);
		// ||_,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		// ||0x80,_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		// ||_,_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		// ||_,_,0x80,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		// ||_,0x80,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||0x80,_,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		// ||_,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		st := block_0_0x033d(st);
		return st;
	}

	method block_0_0x033d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x033d
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(4) == 0x60 && st'.Peek(5) == 0x2f5)
	{
		var st := st';
		// ||_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||_,_,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		// ||_,_,_,_,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||_,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x1f);
		// ||0x1f,_,_,_,_,0x60,0x2f5,_|
		st := And(st);
		// ||_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||_,_,_,_,_,0x60,0x2f5,_|
		st := IsZero(st);
		// ||_,_,_,_,_,0x60,0x2f5,_|
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
	requires (st'.Peek(0) == 0x362 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
	{
		var st := st';
		// ||0x362,_,_,_,_,_,0x60,0x2f5,_|
		assume st.IsJumpDest(0x362);
		st := JumpI(st);
		if st.PC() == 0x362 { st := block_0_0x0362(st); return st;}
		// ||_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||_,_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,3);
		// ||_,_,_,_,_,_,0x60,0x2f5,_|
		st := Sub(st);
		// ||_,_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||_,_,_,_,_,_,0x60,0x2f5,_|
		st := MLoad(st);
		// ||_,_,_,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x01);
		// ||0x01,_,_,_,_,_,_,0x60,0x2f5,_|
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
	requires (st'.Peek(1) == 0x1 && st'.Peek(8) == 0x60 && st'.Peek(9) == 0x2f5)
	{
		var st := st';
		// ||_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		// ||0x20,_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Sub(st);
		// ||_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Push2(st,0x0100);
		// ||0x100,_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Exp(st);
    assert st.Peek(8) == 0x60 && st.Peek(9) == 0x2f5;
		// ||_,0x01,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Sub(st);
		// ||_,_,_,_,_,_,_,0x60,0x2f5,_|
		st := Not(st);
		// ||_,_,_,_,_,_,_,0x60,0x2f5,_|
		st := And(st);
		// ||_,_,_,_,_,_,0x60,0x2f5,_|
		st := Dup(st,2);
		st := block_0_0x035c(st);
		return st;
	}

	method block_0_0x035c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x035c
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires (st'.Peek(7) == 0x60 && st'.Peek(8) == 0x2f5)
	{
		var st := st';
		// ||_,_,_,_,_,_,_,0x60,0x2f5,_|
		st := MStore(st);
		// ||_,_,_,_,_,0x60,0x2f5,_|
		st := Push1(st,0x20);
		// ||0x20,_,_,_,_,_,0x60,0x2f5,_|
		st := Add(st);
		// ||_,_,_,_,_,0x60,0x2f5,_|
		st := Swap(st,2);
		// ||_,_,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		// ||_,_,_,_,0x60,0x2f5,_|
		st := block_0_0x0362(st);
		return st;
	}

	method block_0_0x0362(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0362
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(4) == 0x60 && st'.Peek(5) == 0x2f5)
	{
		var st := st';
		// ||_,_,_,_,0x60,0x2f5,_|
		st := JumpDest(st);
		// ||_,_,_,_,0x60,0x2f5,_|
		st := Pop(st);
		// ||_,_,_,0x60,0x2f5,_|
		st := Swap(st,3);
		// ||0x60,_,_,_,0x2f5,_|
		st := Pop(st);
		// ||_,_,_,0x2f5,_|
		st := Pop(st);
		// ||_,_,0x2f5,_|
		st := Pop(st);
		// ||_,0x2f5,_|
		st := Push1(st,0x40);
		// ||0x40,_,0x2f5,_|
		st := MLoad(st);
		st := block_0_0x036b(st);
		return st;
	}

	method block_0_0x036b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x036b
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x2f5)
	{
		var st := st';
		// ||_,_,0x2f5,_|
		st := Dup(st,1);
		// ||_,_,_,0x2f5,_|
		st := Swap(st,2);
		// ||_,_,_,0x2f5,_|
		st := Sub(st);
		// ||_,_,0x2f5,_|
		st := Swap(st,1);
		// ||_,_,0x2f5,_|
		st := Return(st);
		return st;
	}

	method block_0_0x0b30(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b30
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0x2f5)
  // Termination
  requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.      
	{
		var st := st';
		// |fp=0x0060|0x2f5,_|
		st := JumpDest(st);
		// |fp=0x0060|0x2f5,_|
		st := Push1(st,0x01);
		// |fp=0x0060|0x01,0x2f5,_|
		st := Dup(st,1);
		// |fp=0x0060|0x01,0x01,0x2f5,_|
		st := SLoad(st);
		// |fp=0x0060|_,0x01,0x2f5,_|
		st := Push1(st,0x01);
		// |fp=0x0060|0x01,_,0x01,0x2f5,_|
		st := Dup(st,2);
		// |fp=0x0060|_,0x01,_,0x01,0x2f5,_|
		st := Push1(st,0x01);
		// |fp=0x0060|0x01,_,0x01,_,0x01,0x2f5,_|
		st := AndU1(st);
		st := block_0_0x0b3b(st);
		return st;
	}

	method block_0_0x0b3b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b3b
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
  requires st'.Peek(0) == 0
  requires st'.Peek(2) == st'.Load(0x01)
	requires (st'.Peek(1) == 0x1 && st'.Peek(3) == 0x1 && st'.Peek(4) == 0x2f5)
  // Termination
  requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.    
	{
		var st := st';
		// |fp=0x0060|{0,1},0x01,_,0x01,0x2f5,_|
		st := IsZero(st);
		// |fp=0x0060|{1,0},0x01,_,0x01,0x2f5,_|
		st := Push2(st,0x0100);
		// |fp=0x0060|0x100,_,0x01,_,0x01,0x2f5,_|
		st := Mul(st);
		// |fp=0x0060|_,0x01,_,0x01,0x2f5,_|
		st := Sub(st);
    assert st.Peek(2) == 0x1 && st.Peek(3) == 0x2f5;
		// |fp=0x0060|_,_,0x01,0x2f5,_|
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
		// |fp=0x0060|_,0x01,0x2f5,_|
		st := Push1(st,0x02);
		// |fp=0x0060|0x02,_,0x01,0x2f5,_|
		st := Swap(st,1);
		// |fp=0x0060|_,0x02,0x01,0x2f5,_|
		st := Div(st);
		st := block_0_0x0b46(st);
		return st;
	}

	method block_0_0x0b46(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b46
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(1) == 0x1 && st'.Peek(2) == 0x2f5)
  requires (st'.Peek(0) == 0x4)
  // Termination
  requires st'.Load(1) == 4 * 2 // length of "WETH", shifted left.  
	{
		var st := st';
		// |fp=0x0060|len,0x01,0x2f5,_|
		st := Dup(st,1);
		// |fp=0x0060|len,len,0x01,0x2f5,_|
		st := Push1(st,0x1f);
		// |fp=0x0060|0x1f,len,len,0x01,0x2f5,_|
		st := Add(st);
		// |fp=0x0060|len+0x1f,len,0x01,0x2f5,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,len+0x1f,len,0x01,0x2f5,_|
		st := Dup(st,1);
		// |fp=0x0060|0x20,0x20,len+0x1f,len,0x01,0x2f5,_|
		st := Swap(st,2);
		// |fp=0x0060|len+0x1f,0x20,0x20,len,0x01,0x2f5,_|
		st := Div(st);
		// |fp=0x0060|?,0x20,m,0x01,0x2f5,_|
		st := Mul(st);
		// |fp=0x0060|n,len,0x01,0x2f5,_|    
		st := block_0_0x0b50(st);
		return st;
	}

	method block_0_0x0b50(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b50
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(2) == 0x1 && st'.Peek(3) == 0x2f5)
  // Termination
  requires st'.Load(1) == 4 * 2 // length of "WETH", shifted left.
  requires st'.Peek(0) < 0xffff - 0x80
  requires st'.Peek(1) < 0xffff
	{
		var st := st';
		// |fp=0x0060|?fp,m,0x01,0x2f5,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,?fp,m,0x01,0x2f5,_|
		st := Add(st);
		// |fp=0x0060|?fp+20,m,0x01,0x2f5,_|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,?fp+20,m,0x01,0x2f5,_|
		st := MLoad(st);
    assert st.Peek(2) < 0xffff;
		// |fp=0x0060|0x60,?fp+20,m,0x01,0x2f5,_|
		st := Swap(st,1);
		// |fp=0x0060|?fp+20,0x60,m,0x01,0x2f5,_|
		st := Dup(st,2);
		// |fp=0x0060|0x60,?fp+20,0x60,m,0x01,0x2f5,_|
		st := Add(st);
		// |fp=0x0060|?fp+0x80,0x60,m,0x01,0x2f5,_|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,?fp+0x80,0x60,m,0x01,0x2f5,_|    
		st := block_0_0x0b5b(st);
		return st;
	}

	method block_0_0x0b5b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b5b
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(0) == 0x40 && st'.Peek(2) == 0x60 && st'.Peek(4) == 0x1 && st'.Peek(5) == 0x2f5)
  // Termination
	requires (0x80 <= st'.Peek(1) < 0xffff)
  requires (st'.Peek(3) < 0xffff)
  requires st'.Load(1) == 4 * 2 // length of "WETH", shifted left.    
	{
		var st := st';
		// |fp=0x0060|0x40,_,0x60,?nf,0x01,0x2f5,_|
		st := MStore(st);
		// ||0x60,?nf,0x01,0x2f5,_|    
    assert st.Read(0x40) == st'.Peek(1);
    //
		st := Dup(st,1);
		// ||0x60,0x60,?nf,0x01,0x2f5,_|
		st := Swap(st,3);
		// ||0x01,0x60,?nf,0x60,0x2f5,_|
		st := Swap(st,2);
		// ||?nf,0x60,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||0x60,?nf,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||?nf,0x60,_,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||0x60,?nf,0x60,_,0x01,0x60,0x2f5,_|
		st := MStore(st);
		st := block_0_0x0b63(st);
		return st;
	}

	method block_0_0x0b63(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b63
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff            
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(2) == 0x1 && st'.Peek(3) == 0x60 && st'.Peek(4) == 0x2f5)
  // Termination
	requires (st'.Read(0x60) <= 0xffff)
  requires st'.Load(1) == 4 * 2 // length of "WETH", shifted left.  
	{
		var st := st';
		// ||0x60,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x20);
		// ||0x20,0x60,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		// ||0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,3);
		// ||0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||0x01,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := SLoad(st);
		// ||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x01);
		// ||0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||_,0x01,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x01);
		st := block_0_0x0b6e(st);
		return st;
	}

	method block_0_0x0b6e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b6e
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff          
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(0) == 0x1 && st'.Peek(2) == 0x1 && st'.Peek(4) == 0x1 && st'.Peek(5) == 0x80 && st'.Peek(7) == 0x1 && st'.Peek(8) == 0x60 && st'.Peek(9) == 0x2f5)
  requires st'.Peek(3) == st'.Load(1)
  // Termination
	requires (st'.Read(0x60) <= 0xffff)
  requires st'.Load(1) == 4 * 2 // length of "WETH", shifted left.  
	{
		var st := st';
		// ||0x01,_,0x01,s0,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := AndU1(st);
		// ||_,0x01,s0,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := IsZero(st);
		// ||_,0x01,s0,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0100);
		// ||0x100,_,0x01,s0,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Mul(st);
    assert st.Peek(3) == st.Peek(6) == 0x1 && st.Peek(7) == 0x60 && st.Peek(8) == 0x2f5;
		// ||_,0x01,s0,0x01,0x80,_,0x01,0x60,0x2f5,_|    
		st := Sub(st);
		// ||_,s0,0x01,0x80,_,0x01,0x60,0x2f5,_|		    
    var x := st.Peek(1);
		assert st.Peek(0) in {MAX_U256 as u256, 0xFF};
    assert st.Peek(1) == 4 * 2;
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
    assert st.Peek(0) <= x;
		// ||2n,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x02);
		// ||0x02,2n,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||2n,0x02,0x01,0x80,_,0x01,0x60,0x2f5,_|    
		st := block_0_0x0b79(st);
		return st;
	}

	method block_0_0x0b79(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b79
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff        
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(1) == 0x2 && st'.Peek(2) == 0x1 && st'.Peek(3) == 0x80 && st'.Peek(5) == 0x1 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
  requires st'.Peek(0) == st'.Load(1)
  // Termination
	requires st'.Read(0x60) <= 0xffff
  requires st'.Load(1) == 4 * 2 // length of "WETH", shifted left.
	{
		var st := st';
		// ||2*l,0x02,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Div(st);
		// ||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := IsZero(st);
		// ||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0bc6);
		// ||0xbc6,_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		assume st.IsJumpDest(0xbc6);
		st := JumpI(st);
		if st.PC() == 0xbc6 { st := block_0_0x0bc6(st); return st;}
    assert st.Peek(6) == 0x2f5;
		// ||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x1f);
		// ||0x1f,_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|    
		st := Lt(st);
		// ||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|    
		st := block_0_0x0b84(st);
		return st;
	}

	method block_0_0x0b84(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b84
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff      
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
  requires (st'.Peek(0) in {0,1}) && (st'.Peek(0) == 1 <==> 0x1f < st'.Peek(1))  
	requires (st'.Peek(2) == 0x1 && st'.Peek(3) == 0x80 && st'.Peek(5) == 0x1 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
  // Termination
  requires (st'.Peek(1) == 4)
	requires (st'.Read(0x60) <= 0xffff)   
	{
		var st := st';
		// ||_,n,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0b9b);
		// ||0xb9b,_,n,0x01,0x80,_,0x01,0x60,0x2f5,_|
		assume st.IsJumpDest(0xb9b);
		st := JumpI(st);
		if st.PC() == 0xb9b {
      // l >= 0x1f
			//
			// Deadcode begins here.  The reason is that the following code is used
			// to account for copying strings whose length exceeds 31 bytes.
			// However, the actual length of the string involved in this case
			// ("WETH") is only 4 bytes.
      assert false;
      st := block_0_0x0b9b(st); return st;
    }
		// ||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0100);
    assert st.Peek(3) == 0x80 && st.Peek(5) == 0x01 && st.Peek(7) == 0x2f5;    
		// ||0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||0x100,0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,4);
		// ||0x01,0x100,0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := SLoad(st);
    assert st.Peek(7) == 0x01 && st.Peek(8) == 0x60 && st.Peek(9) == 0x2f5;        
		// ||_,0x100,0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Div(st);
		// ||_,0x100,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Mul(st);
		st := block_0_0x0b90(st);
		return st;
	}

	method block_0_0x0b90(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b90
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff    
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x1 && st'.Peek(3) == 0x80 && st'.Peek(5) == 0x1 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
  // Termination
	requires (st'.Read(0x60) <= 0xffff)      
	{
		var st := st';
		// ||_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,4);
		// ||0x80,_,_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := MStore(st);
		// ||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Swap(st,2);
		// ||0x80,0x01,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x20);
		// ||0x20,0x80,0x01,_,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		// ||0xa0,0x01,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,2);
		// ||_,0x01,0xa0,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0bc6);
		// ||0xbc6,_,0x01,0xa0,_,0x01,0x60,0x2f5,_|
		assume st.IsJumpDest(0xbc6);
		st := Jump(st);
		st := block_0_0x0bc6(st);
		return st;
	}

	method block_0_0x0b9b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b9b
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff  
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(1) == 0x1 && st'.Peek(2) == 0x80 && st'.Peek(4) == 0x1 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
  // Termination
  requires st'.Peek(0) == 0x4 // "WETH"
	requires (st'.Read(0x60) <= 0xffff)    
	{
		var st := st';
		// ||n,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := JumpDest(st);
		// ||n,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Dup(st,3);
		// ||0x80,n,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Add(st);
    var n := st.Peek(0);
		// ||n,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Swap(st,2);
		// ||0x80,0x01,n,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||0x01,0x80,n,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x00);
		// ||0x00,0x01,0x80,n,_,0x01,0x60,0x2f5,_|
		st := MStore(st);
		// ||0x80,n,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x20);
    // ||0x20,0x80,n,_,0x01,0x60,0x2f5,_|    
		st := block_0_0x0ba5(n,st); // FIXME
		return st;
	}

	method block_0_0x0ba5(n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ba5
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff  
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x80 && st'.Peek(4) == 0x1 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
  // Termination
	requires (st'.Read(0x60) <= 0xffff)  
  requires (0x80 <= st'.Peek(2) == n < 0xffff)
	{
		var st := st';
		// ||0x20,0x80,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x00);
		// ||0x00,0x20,0x80,_,_,0x01,0x60,0x2f5,_|
		st := Keccak256(st);
		// ||_,0x80,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||0x80,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := block_0_0x0ba9(0x80,n,st);
		return st;
	}

	method block_0_0x0ba9(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ba9
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(4) == 0x1 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
  requires (st'.Peek(0) == i && st'.Peek(2) == n)
  // Termination
	requires (st'.Read(0x60) <= 0xffff)
	requires 0x80 <= i <= n < 0xffff
	decreases n-i,2
	{
		var st := st';
		// ||0x80,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := JumpDest(st);
		// ||0x80,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||_,0x80,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := SLoad(st);
		// ||_,0x80,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,2);
		// ||0x80,_,0x80,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := MStore(st);
		// ||0x80,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||_,0x80,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x01);
		// ||0x01,_,0x80,_,_,0x01,0x60,0x2f5,_|
		// ||0x01,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		st := block_0_0x0bb2(i,n,st);
		return st;
	}

	method block_0_0x0bb2(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bb2
  // Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(4) == 0x1 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
  requires (st'.Peek(1) == i && st'.Peek(2) == n)
  // Termination
	requires (st'.Read(0x60) <= 0xffff)
	requires 0x80 <= i <= n < 0xffff
	decreases n-i,1
	{
		var st := st';
		// ||_,0x80,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		// Havoc 0
		// ||_,0x80,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||0x80,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x20);
		// ||0x20,0x80,_,_,_,0x01,0x60,0x2f5,_|
		// ||0x20,_,_,_,_,0x01,0x60,0x2f5,_|
    assert st.Peek(7) == 0x02f5;
		st := Add(st);
		// ||0xa0,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		// Havoc 0
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,1);
		// ||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,4);
		// ||_,_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Gt(st);
		st := block_0_0x0bb9(i+0x20,n,st);
		return st;
	}

	method block_0_0x0bb9(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bb9
  // Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff  
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(5) == 0x1 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
  requires (st'.Peek(0) in {0,1}) && (st'.Peek(0) == 0 <==> n <= i)
	requires (st'.Peek(1) == i && st'.Peek(3) == n)
  // Termination
	requires (st'.Read(0x60) <= 0xffff)
  requires n < 0xffff && 0xA0 <= i <= (n+0x20)
	decreases n+0x20-i,0  
	{
		var st := st';
		// ||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Push2(st,0x0ba9);
		// ||0xba9,_,_,_,_,_,0x01,0x60,0x2f5,_|
		assume st.IsJumpDest(0xba9);
		st := JumpI(st);
		if st.PC() == 0xba9 { st := block_0_0x0ba9(i,n,st); return st;}
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,3);
		// ||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,1);
		// ||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Sub(st);
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Push1(st,0x1f);
		// ||0x1f,_,_,_,_,0x01,0x60,0x2f5,_|
		st := AndU5(st);
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Dup(st,3);
		st := block_0_0x0bc4(st);
		return st;
	}

	method block_0_0x0bc4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bc4
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff  
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(5) == 0x1 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0x2f5)
  // Termination
	requires (st'.Read(0x60) <= 0xffff)    
	{
		var st := st';
		// ||_,_,_,_,_,0x01,0x60,0x2f5,_|
		st := Add(st);
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		st := Swap(st,2);
		// ||_,0x01,0xa0,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := block_0_0x0bc6(st);
		return st;
	}

	method block_0_0x0bc6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bc6
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(4) == 0x1 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0x2f5)
  // Termination
	requires (st'.Read(0x60) <= 0xffff)  
	{
		var st := st';
		// ||_,0x01,0xa0,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := JumpDest(st);
		// ||_,0x01,0xa0,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,_,0x01,0x60,0x2f5,_|
		// ||_,0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Pop(st);
		// ||0x01,0xa0,_,0x01,0x60,0x2f5,_|
		// ||_,_,_,0x01,0x60,0x2f5,_|
		// ||0x01,0x80,_,0x01,0x60,0x2f5,_|
		st := Pop(st);
		// ||0xa0,_,0x01,0x60,0x2f5,_|
		// ||_,_,0x01,0x60,0x2f5,_|
		// ||0x80,_,0x01,0x60,0x2f5,_|
		st := Pop(st);
		// ||_,0x01,0x60,0x2f5,_|
		st := Pop(st);
		// ||0x01,0x60,0x2f5,_|
		st := Pop(st);
		// ||0x60,0x2f5,_|
		st := Dup(st,2);
		// ||0x2f5,0x60,0x2f5,_|
		assume st.IsJumpDest(0x2f5);
		st := Jump(st);
		st := block_0_0x02f5(st);
		return st;
	}

}
