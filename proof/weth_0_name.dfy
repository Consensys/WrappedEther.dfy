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
	// Storate Items
	requires st'.Load(0) < 0xffff // length of "Wrapped Ether"
	{
		var st := st';
		// |fp=0x0060|_|
		st := JumpDest(st);
		// |fp=0x0060|_|
		st := CallValue(st);
		// |fp=0x0060|_,_|
		st := IsZero(st);
		// |fp=0x0060|_,_|
		st := Push2(st,0x00c4);
		// |fp=0x0060|0xc4,_,_|
		assume st.IsJumpDest(0xc4);
		st := JumpI(st);
		if st.PC() == 0xc4 { st := block_0_0x00c4(st); return st;}
		// |fp=0x0060|_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,_|
		st := Dup(st,1);
		// |fp=0x0060|0x00,0x00,_|
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
	// Storate Items
	requires st'.Load(0) < 0xffff // length of "Wrapped Ether"
	{
		var st := st';
		// |fp=0x0060|_|
		st := JumpDest(st);
		// |fp=0x0060|_|
		st := Push2(st,0x00cc);
		// |fp=0x0060|0xcc,_|
		st := Push2(st,0x04dd);
		// |fp=0x0060|0x4dd,0xcc,_|
		assume st.IsJumpDest(0x4dd);
		st := Jump(st);
		st := block_0_0x04dd(st);
		return st;
	}

	method block_0_0x00cc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00cc
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(1) == 0xcc)	
	requires (st'.Read(0x60) <= 0xffff)
	{
		var st := st';
		// ||0x60,0xcc,_|
		st := JumpDest(st);
		// ||0x60,0xcc,_|
		st := Push1(st,0x40);
		// ||0x40,0x60,0xcc,_|
		st := MLoad(st);
		// ||fp,0x60,0xcc,_|
		st := Dup(st,1);
		// ||fp,fp,0x60,0xcc,_|
		st := Dup(st,1);
		// ||fp,fp,fp,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,fp,fp,fp,0x60,0xcc,_|
		st := Add(st);
		// ||fp+0x20,fp,fp,0x60,0xcc,_|
		st := Dup(st,3);
		// ||fp,fp+020,fp,fp,0x60,0xcc,_|
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
		// ||p,q,p,p,0x60,0xcc,_|
		st := Dup(st,2);
		// ||q,p,q,p,p,0x60,0xcc,_|
		st := Sub(st);
		// ||0x20,q,p,p,0x60,0xcc,_|
		st := Dup(st,3);
		// ||p,0x20,q,p,p,0x60,0xcc,_|
		st := MStore(st);
		assert st.Read(0x60) == st'.Read(0x60);
		// ||q,p,p,0x60,0xcc,_|
		st := Dup(st,4);
		// ||0x60,q,p,p,0x60,0xcc,_|
		st := Dup(st,2);
		// ||q,0x60,q,p,p,0x60,0xcc,_|
		st := Dup(st,2);
		// ||0x60,q,0x60,q,p,p,0x60,0xcc,_|
		st := MLoad(st);
		// ||x,q,0x60,p,_,_,0x60,0xcc,_|				
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
	requires var p := st'.Peek(1); p >= 0x80
	{
		var st := st';
		// ||x,p,0x60,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		// ||p,x,p,0x60,_,_,_,0x60,0xcc,_|
		st := MStore(st);
		// ||p,0x60,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,p,0x60,_,_,_,0x60,0xcc,_|
		st := Add(st);
		assert st.Read(0x60) == st'.Read(0x60);
		// ||p+0x20,0x60,_,_,_,0x60,0xcc,_|
		st := Swap(st,2);
		// ||_,0x60,p+0x20,_,_,0x60,0xcc,_|
		st := Pop(st);
		// ||0x60,p+0x20,_,_,0x60,0xcc,_|
		st := Dup(st,1);
		// ||0x60,0x60,p+0x20,_,_,0x60,0xcc,_|
		st := MLoad(st);
		// ||x,0x60,p+0x20,_,_,0x60,0xcc,_|
		assert st.Peek(0) == st.Read(0x60);
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
	{
		var st := st';
		// ||x,0x60,_,_,_,0x60,0xcc,_|
		st := Swap(st,1);
		// ||0x60,x,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,0x60,x,_,_,_,0x60,0xcc,_|
		st := Add(st);
		// ||0x80,x,_,_,_,0x60,0xcc,_|
		st := Swap(st,1);
		// ||x,0x80,_,_,_,0x60,0xcc,_|
		assert st.Peek(0) == st'.Peek(0);
		st := Dup(st,1);
		// ||x,x,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,4);
		// ||_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,4);
		// ||0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x00);
		// ||0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		assert st.Peek(3) == st'.Peek(0);
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
	// Termination
	requires var y := st'.Peek(0); y as nat == i * 0x20
	requires var x := st'.Peek(3); x <= 0xffff
	requires var x := st'.Peek(3); var y := st'.Peek(0); y <= (x+0x1f)
	decreases var x := st'.Peek(3); var y := st'.Peek(0); (x+0x1f) - y,2
	{
		var st := st';
		// ||0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := JumpDest(st);
		// ||0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,4);
		// ||x,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||x,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		// ||0x00,x,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,x,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		assert st.Peek(12) == 0xcc;
		st := Lt(st); // y < x
		// ||_,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||_,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := IsZero(st);
		// ||_,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||_,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Push2(st,0x010c);
		// ||0x10c,_,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||0x10c,_,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		assume st.IsJumpDest(0x10c);
		st := JumpI(st);
		if st.PC() == 0x10c { st := block_0_0x010c(st); return st;} // if y >= x
		// ||0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,1);
		// ||0x00,0x00,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		assert st'.Peek(0) == st.Peek(1) && st'.Peek(3) == st.Peek(4);
		st := block_0_0x00fb(i,st);
		return st;
	}

	method block_0_0x00fb(i: nat, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00fb
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires (st'.Peek(2) == 0x80 && st'.Peek(6) == 0x80 && st'.Peek(10) == 0x60 && st'.Peek(11) == 0xcc)
	// Termination
	requires var y := st'.Peek(1); y as nat == i * 0x20
	requires var x := st'.Peek(4); var y := st'.Peek(1); y < x <= 0xffff
	decreases var x := st'.Peek(4); var y := st'.Peek(1); x-y,1
	{
		var st := st';
		// ||0x00,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||_,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,3);
		// ||0x80,0x00,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||0x80,y,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Add(st);
		// ||0x80,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y+0x80,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := MLoad(st);
		// ||_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||_,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		assert st'.Peek(1) == st.Peek(2) && st'.Peek(4) == st.Peek(5);
		assert st.Peek(3) == st.Peek(7) == 0x80;
		assert st.Peek(11) == 0x60;
		assert st.Peek(12) == 0xcc;
		// ||0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,_,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,5);
		// ||_,0x00,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||_,y,_,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Add(st);
		// ||_,_,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||_,_,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := MStore(st);
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
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
	// Termination
	requires var y := st'.Peek(1); y as nat == i * 0x20
	requires var x := st'.Peek(4); var y := st'.Peek(1); y < x <= 0xffff
	decreases var x := st'.Peek(4); var y := st'.Peek(1); x-y,0
	{
		var st := st';
		// ||0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		// ||0x00,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		// Havoc 0
		// ||_,0x20,0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||y,0x20,y,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
		st := Add(st);
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
		assume st.IsJumpDest(0xf1);
		st := Jump(st);
		// ||y+0x20,0x80,_,x,_,0x80,_,_,_,0x60,0xcc,_|
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
	{
		var st := st';
		// ||_,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		st := JumpDest(st);
		// ||_,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		// ||0x00,0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		st := Pop(st);
		// ||0x80,_,_,_,0x80,_,_,_,0x60,0xcc,_|
		st := Pop(st);
		// ||_,_,_,0x80,_,_,_,0x60,0xcc,_|
		assert st.Operands() == 10;
		st := Pop(st);
		// ||_,_,0x80,_,_,_,0x60,0xcc,_|
		st := Pop(st);
		// ||_,0x80,_,_,_,0x60,0xcc,_|
		st := Swap(st,1);
		// ||0x80,_,_,_,_,0x60,0xcc,_|
		st := Pop(st);
		// ||_,_,_,_,0x60,0xcc,_|
		st := Swap(st,1);
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
	{
		var st := st';
		// ||_,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
		// ||_,_,_,_,_,0x60,0xcc,_|
		st := Add(st);
		// ||_,_,_,_,0x60,0xcc,_|
		st := Swap(st,1);
		// ||_,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x1f);
		// ||0x1f,_,_,_,_,0x60,0xcc,_|
		st := AndU5(st);
		// ||_,_,_,_,0x60,0xcc,_|
		st := Dup(st,1);
		// ||_,_,_,_,_,0x60,0xcc,_|
		st := IsZero(st);
		// ||_,_,_,_,_,0x60,0xcc,_|
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
	requires (st'.Peek(0) == 0x139 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	{
		var st := st';
		// ||0x139,_,_,_,_,_,0x60,0xcc,_|
		assume st.IsJumpDest(0x139);
		st := JumpI(st);
		if st.PC() == 0x139 { st := block_0_0x0139(st); return st;}
		// ||_,_,_,_,0x60,0xcc,_|
		st := Dup(st,1);
		// ||_,_,_,_,_,0x60,0xcc,_|
		st := Dup(st,3);
		// ||_,_,_,_,_,_,0x60,0xcc,_|
		st := Sub(st);
		// ||_,_,_,_,_,0x60,0xcc,_|
		st := Dup(st,1);
		// ||_,_,_,_,_,_,0x60,0xcc,_|
		st := MLoad(st);
		// ||_,_,_,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x01);
		// ||0x01,_,_,_,_,_,_,0x60,0xcc,_|
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
	requires (st'.Peek(1) == 0x1 && st'.Peek(8) == 0x60 && st'.Peek(9) == 0xcc)
	{
		var st := st';
		// ||_,0x01,_,_,_,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,_,0x01,_,_,_,_,_,_,0x60,0xcc,_|
		st := Sub(st);
		// ||_,0x01,_,_,_,_,_,_,0x60,0xcc,_|
		st := Push2(st,0x0100);
		// ||0x100,_,0x01,_,_,_,_,_,_,0x60,0xcc,_|
		assert st.Peek(9) == 0x60 && st.Peek(10) == 0xcc;
		st := Exp(st);
		// ||_,0x01,_,_,_,_,_,_,0x60,0xcc,_|
		st := Sub(st);
		// ||_,_,_,_,_,_,_,0x60,0xcc,_|
		st := Not(st);
		// ||_,_,_,_,_,_,_,0x60,0xcc,_|
		st := And(st);
		// ||_,_,_,_,_,_,0x60,0xcc,_|
		st := Dup(st,2);
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
	{
		var st := st';
		// ||_,_,_,_,_,_,_,0x60,0xcc,_|
		st := MStore(st);
		// ||_,_,_,_,_,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,_,_,_,_,_,0x60,0xcc,_|
		st := Add(st);
		// ||_,_,_,_,_,0x60,0xcc,_|
		st := Swap(st,2);
		// ||_,_,_,_,_,0x60,0xcc,_|
		st := Pop(st);
		// ||_,_,_,_,0x60,0xcc,_|
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
	{
		var st := st';
		// ||_,_,_,_,0x60,0xcc,_|
		st := JumpDest(st);
		// ||_,_,_,_,0x60,0xcc,_|
		st := Pop(st);
		// ||_,_,_,0x60,0xcc,_|
		st := Swap(st,3);
		// ||0x60,_,_,_,0xcc,_|
		st := Pop(st);
		// ||_,_,_,0xcc,_|
		st := Pop(st);
		// ||_,_,0xcc,_|
		st := Pop(st);
		// ||_,0xcc,_|
		st := Push1(st,0x40);
		// ||0x40,_,0xcc,_|
		st := MLoad(st);
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
	{
		var st := st';
		// ||_,_,0xcc,_|
		st := Dup(st,1);
		// ||_,_,_,0xcc,_|
		st := Swap(st,2);
		// ||_,_,_,0xcc,_|
		st := Sub(st);
		// ||_,_,0xcc,_|
		st := Swap(st,1);
		// ||_,_,0xcc,_|
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
	requires st'.Load(0) < 0xffff // length of "Wrapped Ether"
	{
		var st := st';
		// |fp=0x0060|0xcc,_|
		st := JumpDest(st);
		// |fp=0x0060|0xcc,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0xcc,_|
		st := Dup(st,1);
		// |fp=0x0060|0x00,0x00,0xcc,_|
		st := SLoad(st);		
		// |fp=0x0060|s0,0x00,0xcc,_|
		st := Push1(st,0x01);
		// |fp=0x0060|0x01,s0,0x00,0xcc,_|
		st := Dup(st,2);
		// |fp=0x0060|s0,0x01,s0,0x00,0xcc,_|
		st := Push1(st,0x01);
		// |fp=0x0060|0x01,s0,0x01,s0,0x00,0xcc,_|
		st := AndU1(st);
		assert st.Peek(0) in {0x00,0x1};
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
	requires st'.Peek(0) in {0,1}
	requires st'.Peek(2) == st'.Load(0x00)
	requires (st'.Peek(1) == 0x1 && st'.Peek(3) == 0x0 && st'.Peek(4) == 0xcc)
	// Storate Items
	requires st'.Load(0) < 0xffff // length of "Wrapped Ether"
	{
		var st := st';
		// |fp=0x0060|{0,1},0x01,s0,0x00,0xcc,_|
		st := IsZero(st);
		// |fp=0x0060|{1,0},0x01,s0,0x00,0xcc,_|
		st := Push2(st,0x0100);
		// |fp=0x0060|0x100,{1,0},0x01,s0,0x00,0xcc,_|
		st := Mul(st);
		// |fp=0x0060|{0x100,0},0x01,s0,0x00,0xcc,_|
		st := Sub(st);
		// |fp=0x0060|_,s0,0x00,0xcc,_|
		var x := st.Peek(1);
		assert st.Peek(0) in {MAX_U256 as u256, 0xFF};
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
		assert st.Peek(0) <= x;
		// |fp=0x0060|s0&,0x00,0xcc,_|
		st := Push1(st,0x02);
		// |fp=0x0060|0x02,l2,0x00,0xcc,_|
		st := Swap(st,1);
		// |fp=0x0060|l2,0x02,0x00,0xcc,_|
		st := Div(st);
		// |fp=0x0060|len,0x00,0xcc,_| // len=length of array (in bytes)
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
	requires (st'.Peek(0) < 0xff00)
	{
		var st := st';
		// |fp=0x0060|len,0x00,0xcc,_|
		st := Dup(st,1);
		// |fp=0x0060|len,len,0x00,0xcc,_|
		st := Push1(st,0x1f);
		// |fp=0x0060|0x1f,len,len,0x00,0xcc,_|
		st := Add(st);
		// |fp=0x0060|len+0x1f,len,0x00,0xcc,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,len+0x1f,len,0x00,0xcc,_|
		assert st.Peek(3) == 0x00 && st.Peek(4) == 0xcc;
		st := Dup(st,1);
		// |fp=0x0060|0x20,0x20,len+0x1f,len,0x00,0xcc,_|
		st := Swap(st,2);
		// |fp=0x0060|len+0x1f,0x20,0x20,len,0x00,0xcc,_|
		st := Div(st);
		var n := st.Peek(0) as nat;
		// |fp=0x0060|n,0x20,len,0x00,0xcc,_|
		st := Mul(st);
		// |fp=0x0060|n*0x20,len,0x20,_,0x00,0xcc,_| // n is len rounded up
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
	requires (st'.Peek(0) < 0xff7f)
	requires (st'.Peek(1) < 0xffff)
	requires (st'.Peek(2) == 0x0 && st'.Peek(3) == 0xcc)
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
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x60 && st'.Peek(4) == 0xcc)
	{
		var st := st';
		// ||0x60,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,0x60,_,0x00,0x60,0xcc,_|
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
	{
		var st := st';
		// ||0x01,_,0x01,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := AndU1(st);
		// ||_,0x01,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := IsZero(st);
		// ||_,0x01,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0100);
		// ||0x100,_,0x01,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Mul(st);
		// ||_,0x01,_,0x00,0x80,_,0x00,0x60,0xcc,_|
    	assert st.Peek(4) == 0x80 && st.Peek(6) == 0x00 && st.Peek(7) == 0x60 && st.Peek(8) == 0xcc;
		st := Sub(st);
		// ||_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := And(st);
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x02);
		// ||0x02,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
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
	{
		var st := st';
		// ||_,0x02,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Div(st);
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,1);
		// ||_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := IsZero(st);
		// ||_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0573);
		// ||0x573,_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		assume st.IsJumpDest(0x573);
		st := JumpI(st);
		if st.PC() == 0x573 { st := block_0_0x0573(st); return st;}
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,1);
		// ||_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x1f);
		// ||0x1f,_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Lt(st);
		st := block_0_0x0531(st);
		return st;
	}

	method block_0_0x0531(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0531
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	requires (st'.Read(0x60) <= 0xffff)	

	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 && st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	{
		var st := st';
		// ||_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0548);
		// ||0x548,_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		assume st.IsJumpDest(0x548);
		st := JumpI(st);
		if st.PC() == 0x548 { st := block_0_0x0548(st); return st;}
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0100);
		// ||0x100,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		assert st.Peek(7) == 0xcc;
		st := Dup(st,1);
		// ||0x100,0x100,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,4);
		// ||0x00,0x100,0x100,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := SLoad(st);
		// ||_,0x100,0x100,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Div(st);
		// ||_,0x100,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Mul(st);
		st := block_0_0x053d(st);
		return st;
	}

	method {:verify false} block_0_0x053d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x053d
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	requires (st'.Read(0x60) <= 0xffff)	
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x0 && st'.Peek(3) == 0x80 && st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	{
		var st := st';
		// ||_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,4);
		// ||0x80,_,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := MStore(st);
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Swap(st,2);
		// ||0x80,0x00,_,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,0x80,0x00,_,_,0x00,0x60,0xcc,_|
		st := Add(st);
		// ||0xa0,0x00,_,_,0x00,0x60,0xcc,_|
		st := Swap(st,2);
		// ||_,0x00,0xa0,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0573);
		// ||0x573,_,0x00,0xa0,_,0x00,0x60,0xcc,_|
		assume st.IsJumpDest(0x573);
		st := Jump(st);
		st := block_0_0x0573(st);
		return st;
	}

	method block_0_0x0548(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0548
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	requires (st'.Read(0x60) <= 0xffff)	
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(1) == 0x0 && st'.Peek(2) == 0x80 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := JumpDest(st);
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Dup(st,3);
		// ||0x80,_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Add(st);
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Swap(st,2);
		// ||0x80,0x00,_,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||0x00,0x80,_,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x00);
		// ||0x00,0x00,0x80,_,_,0x00,0x60,0xcc,_|
		st := MStore(st);
		// ||0x80,_,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x20);
		st := block_0_0x0552(st);
		return st;
	}

	method block_0_0x0552(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0552
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	requires (st'.Read(0x60) <= 0xffff)	
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x80 && st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		// ||0x20,0x80,_,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x00);
		// ||0x00,0x20,0x80,_,_,0x00,0x60,0xcc,_|
		st := Keccak256(st);
		// ||_,0x80,_,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := block_0_0x0556(st);
		return st;
	}

	method {:verify false} block_0_0x0556(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0556
	// Free Memory Pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) <= 0xffff
	requires (st'.Read(0x60) <= 0xffff)	
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		// ||0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := JumpDest(st);
		// ||0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Dup(st,2);
		// ||_,0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,_,0x00,0x60,0xcc,_|
		st := SLoad(st);
		// ||_,0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,_,0x00,0x60,0xcc,_|
		st := Dup(st,2);
		// ||0x80,_,0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,_,_,0x00,0x60,0xcc,_|
		st := MStore(st);
		// ||0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||_,0x80,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x01);
		// ||0x01,_,0x80,_,_,0x00,0x60,0xcc,_|
		// ||0x01,_,_,_,_,0x00,0x60,0xcc,_|
		st := Add(st);
		st := block_0_0x055f(st);
		return st;
	}

	method {:verify false} block_0_0x055f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x055f
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(4) == 0x0 && st'.Peek(5) == 0x60 && st'.Peek(6) == 0xcc)
	{
		var st := st';
		// ||_,0x80,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		// Havoc 0
		// ||_,0x80,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x20);
		// ||0x20,0x80,_,_,_,0x00,0x60,0xcc,_|
		// ||0x20,_,_,_,_,0x00,0x60,0xcc,_|
		st := Add(st);
		// ||0xa0,_,_,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		// Havoc 0
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Dup(st,1);
		// ||_,_,_,_,_,0x00,0x60,0xcc,_|
		st := Dup(st,4);
		// ||_,_,_,_,_,_,0x00,0x60,0xcc,_|
		st := Gt(st);
		st := block_0_0x0566(st);
		return st;
	}

	method {:verify false} block_0_0x0566(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0566
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && 0x80 <= st'.Read(0x40) < 0xffff
	requires (st'.Read(0x60) <= 0xffff)
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(5) == 0x0 && st'.Peek(6) == 0x60 && st'.Peek(7) == 0xcc)
	{
		var st := st';
		// ||_,_,_,_,_,0x00,0x60,0xcc,_|
		st := Push2(st,0x0556);
		// ||0x556,_,_,_,_,_,0x00,0x60,0xcc,_|
		assume st.IsJumpDest(0x556);
		st := JumpI(st);
		if st.PC() == 0x556 { st := block_0_0x0556(st); return st;}
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Dup(st,3);
		// ||_,_,_,_,_,0x00,0x60,0xcc,_|
		st := Swap(st,1);
		// ||_,_,_,_,_,0x00,0x60,0xcc,_|
		st := Sub(st);
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Push1(st,0x1f);
		// ||0x1f,_,_,_,_,0x00,0x60,0xcc,_|
		st := AndU5(st);
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Dup(st,3);
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
	{
		var st := st';
		// ||_,_,_,_,_,0x00,0x60,0xcc,_|
		st := Add(st);
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		st := Swap(st,2);
		// ||_,0x00,0xa0,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
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
		// ||_,0x00,0xa0,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := JumpDest(st);
		// ||_,0x00,0xa0,_,0x00,0x60,0xcc,_|
		// ||_,_,_,_,0x00,0x60,0xcc,_|
		// ||_,0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Pop(st);
		// ||0x00,0xa0,_,0x00,0x60,0xcc,_|
		// ||_,_,_,0x00,0x60,0xcc,_|
		// ||0x00,0x80,_,0x00,0x60,0xcc,_|
		st := Pop(st);
		// ||0xa0,_,0x00,0x60,0xcc,_|
		// ||_,_,0x00,0x60,0xcc,_|
		// ||0x80,_,0x00,0x60,0xcc,_|
		st := Pop(st);
		// ||_,0x00,0x60,0xcc,_|
		st := Pop(st);
		// ||0x00,0x60,0xcc,_|
		st := Pop(st);
		// ||0x60,0xcc,_|
		st := Dup(st,2);
		// ||0xcc,0x60,0xcc,_|
		assume st.IsJumpDest(0xcc);
		st := Jump(st);
		st := block_0_0x00cc(st);
		return st;
	}

}
