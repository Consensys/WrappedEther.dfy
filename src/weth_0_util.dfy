include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module util {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x00b7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00b7
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() >= 0 && st'.Operands() <= 1
	{
		var st := st';
		// |fp=0x0060|_|
		// |fp=0x0060||
		st := JumpDest(st);
		// |fp=0x0060|_|
		// |fp=0x0060||
		st := Stop(st);
		return st;
	}

	method block_0_0x0229(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0229
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0x1)
	{
		var st := st';
		// |fp=0x0060|0x01,_|
		st := JumpDest(st);
		// |fp=0x0060|0x01,_|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0x01,_|
		st := MLoad(st);
		// |fp=0x0060|0x60,0x01,_|
		st := Dup(st,1);
		// |fp=0x0060|0x60,0x60,0x01,_|
		st := Dup(st,3);
		// |fp=0x0060|0x01,0x60,0x60,0x01,_|
		st := IsZero(st);
		// |fp=0x0060|0x00,0x60,0x60,0x01,_|
		st := IsZero(st);
		// |fp=0x0060|0x01,0x60,0x60,0x01,_|
		st := IsZero(st);
		st := block_0_0x0232(st);
		return st;
	}

	method block_0_0x0232(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0232
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	//requires (st'.Peek(0) == 0x0 && st'.Peek(1) == 0x60 && st'.Peek(2) == 0x60 && st'.Peek(3) == 0x1)
	requires (st'.Peek(1) == 0x60)
	{
		var st := st';
		// |fp=0x0060|0x00,0x60,0x60,0x01,_|
		st := IsZero(st);
		// |fp=0x0060|0x01,0x60,0x60,0x01,_|
		st := Dup(st,2);
		// |fp=0x0060|0x60,0x01,0x60,0x60,0x01,_|
		st := MStore(st);
		// |fp=0x0060|0x60,0x60,0x01,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x60,0x60,0x01,_|
		assert 0x20 + 0x60 == 0x80;
		st := Add(st);
		assert st.Peek(0) == 0x80;		
		// |fp=0x0060|0x80,0x60,0x01,_|
		st := Swap(st,2);
		// |fp=0x0060|0x01,0x60,0x80,_|
		st := Pop(st);
		// |fp=0x0060|0x60,0x80,_|
		st := Pop(st);
		// |fp=0x0060|0x80,_|		
		st := block_0_0x023b(st);
		return st;
	}

	method block_0_0x023b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x023b
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0x80)
	{
		var st := st';
		// |fp=0x0060|0x80,_|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0x80,_|
		st := MLoad(st);
		// |fp=0x0060|0x60,0x80,_|
		st := Dup(st,1);
		// |fp=0x0060|0x60,0x60,0x80,_|
		st := Swap(st,2);
		// |fp=0x0060|0x80,0x60,0x60,_|
		st := Sub(st);
		// |fp=0x0060|0x20,0x60,_|
		st := Swap(st,1);
		// |fp=0x0060|0x60,0x20,_|
		st := Return(st);
		return st;
	}

	method block_0_0x03b0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03b0
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0x1)
	{
		var st := st';
		// |fp=0x0060|0x01,_|
		st := JumpDest(st);
		// |fp=0x0060|0x01,_|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0x01,_|
		st := MLoad(st);
		// |fp=0x0060|0x60,0x01,_|
		st := Dup(st,1);
		// |fp=0x0060|0x60,0x60,0x01,_|
		st := Dup(st,3);
		// |fp=0x0060|0x01,0x60,0x60,0x01,_|
		st := IsZero(st);
		// |fp=0x0060|0x00,0x60,0x60,0x01,_|
		st := IsZero(st);
		// |fp=0x0060|0x01,0x60,0x60,0x01,_|
		st := IsZero(st);
		st := block_0_0x03b9(st);
		return st;
	}

	method block_0_0x03b9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03b9
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	//requires (st'.Peek(0) == 0x0 && st'.Peek(1) == 0x60 && st'.Peek(2) == 0x60 && st'.Peek(3) == 0x1)
	requires (st'.Peek(1) == 0x60)
	{
		var st := st';
		// |fp=0x0060|0x00,0x60,0x60,0x01,_|
		st := IsZero(st);
		// |fp=0x0060|0x01,0x60,0x60,0x01,_|
		st := Dup(st,2);
		// |fp=0x0060|0x60,0x01,0x60,0x60,0x01,_|
		st := MStore(st);
		// |fp=0x0060|0x60,0x60,0x01,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x60,0x60,0x01,_|
		st := Add(st);
		assert st.Peek(0) == 0x80;
		// |fp=0x0060|0x80,0x60,0x01,_|
		st := Swap(st,2);
		// |fp=0x0060|0x01,0x60,0x80,_|
		st := Pop(st);
		// |fp=0x0060|0x60,0x80,_|
		st := Pop(st);
		// |fp=0x0060|0x80,_|
		st := block_0_0x03c2(st);
		return st;
	}

	method block_0_0x03c2(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03c2
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0x80)
	{
		var st := st';
		// |fp=0x0060|0x80,_|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0x80,_|
		st := MLoad(st);
		// |fp=0x0060|0x60,0x80,_|
		st := Dup(st,1);
		// |fp=0x0060|0x60,0x60,0x80,_|
		st := Swap(st,2);
		// |fp=0x0060|0x80,0x60,0x60,_|
		st := Sub(st);
		// |fp=0x0060|0x20,0x60,_|
		st := Swap(st,1);
		// |fp=0x0060|0x60,0x20,_|
		st := Return(st);
		return st;
	}

	method block_0_0x03d2(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03d2
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		// |fp=0x0060|_|
		st := JumpDest(st);
		// |fp=0x0060|_|
		st := Stop(st);
		return st;
	}

	method block_0_0x0440(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0440
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() >= 1 && st'.Operands() <= 2
	// Dynamic stack items
	requires st'.Operands() == 1 ==> ((st'.Peek(0) == 0xb7))
	requires st'.Operands() == 2 ==> ((st'.Peek(0) == 0xb7) || (st'.Peek(0) == 0x3d2))
	{
		var st := st';
		// |fp=0x0060|0xb7,_|
		// |fp=0x0060|0x3d2,_|
		// |fp=0x0060|0xb7|
		st := JumpDest(st);
		// |fp=0x0060|0xb7,_|
		// |fp=0x0060|0x3d2,_|
		// |fp=0x0060|0xb7|
		st := CallValue(st);
		// |fp=0x0060|_,0xb7,_|
		// |fp=0x0060|_,0x3d2,_|
		// |fp=0x0060|_,0xb7|
		st := Push1(st,0x03);
		// |fp=0x0060|0x03,_,0xb7,_|
		// |fp=0x0060|0x03,_,0x3d2,_|
		// |fp=0x0060|0x03,_,0xb7|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x03,_,0xb7,_|
		// |fp=0x0060|0x00,0x03,_,0x3d2,_|
		// |fp=0x0060|0x00,0x03,_,0xb7|
		st := Caller(st);
		// |fp=0x0060|_,0x00,0x03,_,0xb7,_|
		// |fp=0x0060|_,0x00,0x03,_,0x3d2,_|
		// |fp=0x0060|_,0x00,0x03,_,0xb7|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0xb7,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x3d2,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0xb7|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x03,_,0xb7,_|
		// |fp=0x0060|_,0x00,0x03,_,0x3d2,_|
		// |fp=0x0060|_,0x00,0x03,_,0xb7|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		st := block_0_0x0472(st);
		return st;
	}

	method {:verify false} block_0_0x0472(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0472
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() >= 6 && st'.Operands() <= 7
	// Static stack items
	requires (st'.Peek(0) == 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff && st'.Peek(2) == 0x0)
	// Dynamic stack items
	requires (st'.Peek(5) == 0xb7) || (st'.Peek(5) == 0x3d2 && st'.Operands() == 7)
	{
		var st := st';
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0xb7,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x3d2,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0xb7|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x03,_,0xb7,_|
		// |fp=0x0060|_,0x00,0x03,_,0x3d2,_|
		// |fp=0x0060|_,0x00,0x03,_,0xb7|
		st := Dup(st,2);
		// |fp=0x0060|0x00,_,0x00,0x03,_,0xb7,_|
		// |fp=0x0060|0x00,_,0x00,0x03,_,0x3d2,_|
		// |fp=0x0060|0x00,_,0x00,0x03,_,0xb7|
		st := MStore(st);
		assert (st.Peek(3) == 0xb7) || (st.Peek(3) == 0x3d2 && st.Operands() == 5);
		// |fp=0x0060|0x00,0x03,_,0xb7,_|
		// |fp=0x0060|0x00,0x03,_,0x3d2,_|
		// |fp=0x0060|0x00,0x03,_,0xb7|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x00,0x03,_,0xb7,_|
		// |fp=0x0060|0x20,0x00,0x03,_,0x3d2,_|
		// |fp=0x0060|0x20,0x00,0x03,_,0xb7|
		st := Add(st);
		assert st.Peek(0) == 0x20;
		// |fp=0x0060|0x20,0x03,_,0xb7,_|
		// |fp=0x0060|0x20,0x03,_,0x3d2,_|
		// |fp=0x0060|0x20,0x03,_,0xb7|
		st := Swap(st,1);
		// |fp=0x0060|0x03,0x20,_,0xb7,_|
		// |fp=0x0060|0x03,0x20,_,0x3d2,_|
		// |fp=0x0060|0x03,0x20,_,0xb7|
		st := Dup(st,2);
		assert (st.Peek(4) == 0xb7) || (st.Peek(4) == 0x3d2 && st.Operands() == 6);
		// |fp=0x0060|0x20,0x03,0x20,_,0xb7,_|
		// |fp=0x0060|0x20,0x03,0x20,_,0x3d2,_|
		// |fp=0x0060|0x20,0x03,0x20,_,0xb7|
		st := MStore(st);
		// |fp=0x0060|0x20,_,0xb7,_|
		// |fp=0x0060|0x20,_,0x3d2,_|
		// |fp=0x0060|0x20,_,0xb7|
		st := block_0_0x047b(st);
		return st;
	}

	method block_0_0x047b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x047b
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3 || st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(0) == 0x20) 
	// Dynamic stack items
	requires (st'.Peek(2) == 0xb7) || (st'.Peek(2) == 0x3d2 && st'.Operands() == 4)
	{
		var st := st';
		// |fp=0x0060|0x20,_,0xb7,_|
		// |fp=0x0060|0x20,_,0x3d2,_|
		// |fp=0x0060|0x20,_,0xb7|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,_,0xb7,_|
		// |fp=0x0060|0x20,0x20,_,0x3d2,_|
		// |fp=0x0060|0x20,0x20,_,0xb7|
		st := Add(st);
		// |fp=0x0060|0x40,_,0xb7,_|
		// |fp=0x0060|0x40,_,0x3d2,_|
		// |fp=0x0060|0x40,_,0xb7|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x40,_,0xb7,_|
		// |fp=0x0060|0x00,0x40,_,0x3d2,_|
		// |fp=0x0060|0x00,0x40,_,0xb7|
		st := Keccak256(st);
		// |fp=0x0060|_,_,0xb7,_|
		// |fp=0x0060|_,_,0x3d2,_|
		// |fp=0x0060|_,_,0xb7|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,_,_,0xb7,_|
		// |fp=0x0060|0x00,_,_,0x3d2,_|
		// |fp=0x0060|0x00,_,_,0xb7|
		st := Dup(st,3);
		// |fp=0x0060|_,0x00,_,_,0xb7,_|
		// |fp=0x0060|_,0x00,_,_,0x3d2,_|
		// |fp=0x0060|_,0x00,_,_,0xb7|
		st := Dup(st,3);
		// |fp=0x0060|_,_,0x00,_,_,0xb7,_|
		// |fp=0x0060|_,_,0x00,_,_,0x3d2,_|
		// |fp=0x0060|_,_,0x00,_,_,0xb7|
		st := SLoad(st);
		st := block_0_0x0486(st);
		return st;
	}

	method block_0_0x0486(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0486
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6 || st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(2) == 0x0)
	// Dynamic stack items
	requires (st'.Peek(5) == 0xb7) || (st'.Peek(5) == 0x3d2 && st'.Operands() == 7)
	{
		var st := st';
		// |fp=0x0060|_,_,0x00,_,_,0xb7,_|
		// |fp=0x0060|_,_,0x00,_,_,0x3d2,_|
		// |fp=0x0060|_,_,0x00,_,_,0xb7|
		st := Add(st);
		// |fp=0x0060|_,0x00,_,_,0xb7,_|
		// |fp=0x0060|_,0x00,_,_,0x3d2,_|
		// |fp=0x0060|_,0x00,_,_,0xb7|
		st := Swap(st,3);
		// |fp=0x0060|_,0x00,_,_,0xb7,_|
		// |fp=0x0060|_,0x00,_,_,0x3d2,_|
		// |fp=0x0060|_,0x00,_,_,0xb7|
		st := Pop(st);
		// |fp=0x0060|0x00,_,_,0xb7,_|
		// |fp=0x0060|0x00,_,_,0x3d2,_|
		// |fp=0x0060|0x00,_,_,0xb7|
		st := Pop(st);
		// |fp=0x0060|_,_,0xb7,_|
		// |fp=0x0060|_,_,0x3d2,_|
		// |fp=0x0060|_,_,0xb7|
		st := Dup(st,2);
		// |fp=0x0060|_,_,_,0xb7,_|
		// |fp=0x0060|_,_,_,0x3d2,_|
		// |fp=0x0060|_,_,_,0xb7|
		st := Swap(st,1);
		// |fp=0x0060|_,_,_,0xb7,_|
		// |fp=0x0060|_,_,_,0x3d2,_|
		// |fp=0x0060|_,_,_,0xb7|
		st := SStore(st);
		// |fp=0x0060|_,0xb7,_|
		// |fp=0x0060|_,0x3d2,_|
		// |fp=0x0060|_,0xb7|
		st := Pop(st);
		st := block_0_0x048e(st);
		return st;
	}

	method block_0_0x048e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x048e
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1 || st'.Operands() == 2
	// Dynamic stack items
	requires (st'.Peek(0) == 0xb7) || (st'.Peek(0) == 0x3d2 && st'.Operands() == 2)
	{
		var st := st';
		// |fp=0x0060|0xb7,_|
		// |fp=0x0060|0x3d2,_|
		// |fp=0x0060|0xb7|
		st := Caller(st);
		// |fp=0x0060|_,0xb7,_|
		// |fp=0x0060|_,0x3d2,_|
		// |fp=0x0060|_,0xb7|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0xb7,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x3d2,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0xb7|
		st := AndU160(st);
		// |fp=0x0060|_,0xb7,_|
		// |fp=0x0060|_,0x3d2,_|
		// |fp=0x0060|_,0xb7|
		st := PushN(st,32,0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c);
		// |fp=0x0060|0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := CallValue(st);
		// |fp=0x0060|_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x40,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x40,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := MLoad(st);
		// |fp=0x0060|0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Dup(st,1);
		st := block_0_0x04cb(st);
		return st;
	}

	method block_0_0x04cb(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04cb
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() >= 6 && st'.Operands() <= 7
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(1) == 0x60) // && st'.Peek(3) == 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c)
	// Dynamic stack items
	requires (st'.Peek(5) == 0xb7) || (st'.Peek(5) == 0x3d2 && st'.Operands() == 7)
	{
		var st := st';
		// |fp=0x0060|0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Dup(st,3);
		// |fp=0x0060|_,0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|_,0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|_,0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Dup(st,2);
		// |fp=0x0060|0x60,_,0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x60,_,0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x60,_,0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := MStore(st);
		// |fp=0x0060|0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		assert (st.Peek(5) == 0xb7) || (st.Peek(5) == 0x3d2);
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x20,0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x20,0x60,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Add(st);
		// |fp=0x0060|0x80,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x80,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x80,0x60,_,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Swap(st,2);
		// |fp=0x0060|_,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|_,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|_,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Pop(st);
		// |fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Pop(st);
		st := block_0_0x04d4(st);
		return st;
	}

	method block_0_0x04d4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04d4
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() >= 4 && st'.Operands() <= 5
	// Static stack items
	requires (st'.Peek(0) == 0x80) // && st'.Peek(1) == 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c)
	// Dynamic stack items
	requires (st'.Peek(3) == 0xb7) || (st'.Peek(3) == 0x3d2 && st'.Operands() == 5)
	{
		var st := st';
		// |fp=0x0060|0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x40,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x40,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := MLoad(st);
		// |fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Dup(st,1);
		// |fp=0x0060|0x60,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x60,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x60,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Swap(st,2);
		// |fp=0x0060|0x80,0x60,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x80,0x60,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x80,0x60,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Sub(st);
		// |fp=0x0060|0x20,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x20,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x20,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := Swap(st,1);
		// |fp=0x0060|0x60,0x20,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7,_|
		// |fp=0x0060|0x60,0x20,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0x3d2,_|
		// |fp=0x0060|0x60,0x20,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,_,0xb7|
		st := LogN(st,2);
		// |fp=0x0060|0xb7,_|
		// |fp=0x0060|0x3d2,_|
		// |fp=0x0060|0xb7|
		assume st.IsJumpDest(0xb7);
		assume st.IsJumpDest(0x3d2);
		st := Jump(st);
		match st.PC() {
			case 0xb7 => { st := block_0_0x00b7(st); }
			case 0x3d2 => { st := block_0_0x03d2(st); }
	}
		return st;
	}

	method block_0_0x068c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x068c
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {5,9}
	// Dynamic stack items
	requires st'.Operands() == 5 ==> ((st'.Peek(3) == 0x229))
	requires st'.Operands() == 9 ==> ((st'.Peek(3) == 0xbdb && st'.Peek(4) == 0x0 && st'.Peek(7) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,_,0x229,_|
		st := JumpDest(st);
		// |fp=0x0060|_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x03);
		// |fp=0x0060|0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x03,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Dup(st,7);
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		st := block_0_0x06ab(st);
		return st;
	}

	method block_0_0x06ab(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06ab
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {10,14}
	// Static stack items
	requires (st'.Peek(1) == 0x0 && st'.Peek(2) == 0x3 && st'.Peek(4) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 10 ==> ((st'.Peek(8) == 0x229))
	requires st'.Operands() == 14 ==> ((st'.Peek(8) == 0xbdb && st'.Peek(9) == 0x0 && st'.Peek(12) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		assert st.Peek(2) == 0x03 && st.Peek(4) == 0x00;
		st := Dup(st,2);
		// |fp=0x0060|0x00,_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0x229,_|
		assert {:split_here} true;
		assert st.Peek(1) == 0x03 && st.Peek(3) == 0x00;
		assert st.Operands() == 9 ==> st.Peek(7) == 0x229;
		assert st.Operands() == 13 ==> (st.Peek(7) == 0xbdb && st.Peek(8) == 0x00 && st.Peek(11) == 0x3b0);
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x20,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x03,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|0x03,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x03,0x20,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		st := block_0_0x06c8(st);
		return st;
	}

	method block_0_0x06c8(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06c8
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {10,14}
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x3 && st'.Peek(2) == 0x20 && st'.Peek(4) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 10 ==> ((st'.Peek(8) == 0x229))
	requires st'.Operands() == 14 ==> ((st'.Peek(8) == 0xbdb && st'.Peek(9) == 0x0 && st'.Peek(12) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x20,0x03,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x03,0x20,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		assert st.Peek(3) == 0x00;
		assert st.Operands() == 13 ==> (st.Peek(7) == 0xbdb && st.Peek(8) == 0x0 && st.Peek(11) == 0x3b0);
		assert st.Operands() == 9 ==> st.Peek(7) == 0x229;
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0x229,_|
		st := Keccak256(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := SLoad(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Lt(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		st := block_0_0x06d2(st);
		return st;
	}

	method block_0_0x06d2(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06d2
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {7,11}
	// Static stack items
	requires (st'.Peek(1) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 7 ==> ((st'.Peek(5) == 0x229))
	requires st'.Operands() == 11 ==> ((st'.Peek(5) == 0xbdb && st'.Peek(6) == 0x0 && st'.Peek(9) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Push2(st,0x06dc);
		// |fp=0x0060|0x6dc,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x6dc,_,0x00,_,_,_,0x229,_|
		assume st.IsJumpDest(0x6dc);
		st := JumpI(st);
		if st.PC() == 0x6dc { st := block_0_0x06dc(st); return st;}
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x00,_,_,_,0x229,_|
		st := Dup(st,1);
		// |fp=0x0060|0x00,0x00,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x00,0x00,_,_,_,0x229,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x06dc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06dc
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {6,10}
	// Static stack items
	requires (st'.Peek(0) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 6 ==> ((st'.Peek(4) == 0x229))
	requires st'.Operands() == 10 ==> ((st'.Peek(4) == 0xbdb && st'.Peek(5) == 0x0 && st'.Peek(8) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := JumpDest(st);
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Caller(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		assert (st.Peek(1) == 0x0);
		assert st.Operands() == 7 ==> ((st.Peek(5) == st'.Peek(4) == 0x229));
		assert st.Operands() == 11 ==> ((st.Peek(5) == 0xbdb && st.Peek(6) == 0x0 && st.Peek(9) == 0x3b0));
		st := Dup(st,5);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
    assert st.Operands() in {9,13};
		assert st.Operands() != 9 || (st.Peek(7) == st'.Peek(4) == 0x229);        
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Eq(st);
		st := block_0_0x070c(st);
		return st;
	}

	method block_0_0x070c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x070c
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {7,11}
	// Static stack items
	requires (st'.Peek(1) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 7 ==> ((st'.Peek(5) == 0x229))
	requires st'.Operands() == 11 ==> ((st'.Peek(5) == 0xbdb && st'.Peek(6) == 0x0 && st'.Peek(9) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Dup(st,1);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Push2(st,0x07b4);
		// |fp=0x0060|0x7b4,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x7b4,_,_,0x00,_,_,_,0x229,_|
		assume st.IsJumpDest(0x7b4);
		st := JumpI(st);
		if st.PC() == 0x7b4 { st := block_0_0x07b4(st); return st;}
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := PushN(st,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Push1(st,0x04);
		st := block_0_0x0737(st);
		return st;
	}

	method block_0_0x0737(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0737
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {8,12}
	// Static stack items
	requires (st'.Peek(0) == 0x4 && st'.Peek(1) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff && st'.Peek(2) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 8 ==> ((st'.Peek(6) == 0x229))
	requires st'.Operands() == 12 ==> ((st'.Peek(6) == 0xbdb && st'.Peek(7) == 0x0 && st'.Peek(10) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Dup(st,7);
		// |fp=0x0060|_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		assert {:split_here} true;
		assert (st.Peek(1) == 0x0 && st.Peek(2) == 0x4 && st.Peek(3) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff && st.Peek(4) == 0x0);
		// Dynamic stack items
		assert st.Operands() == 9 ==> ((st.Peek(8) == 0x229));
		assert st.Operands() == 13 ==> ((st.Peek(8) == 0xbdb && st.Peek(9) == 0x0 && st.Peek(12) == 0x3b0));
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x00,_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := MStore(st);
		st := block_0_0x0768(st);
		return st;
	}

	method block_0_0x0768(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0768
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {9,13}
	// Static stack items
	requires (st'.Peek(0) == 0x0 && st'.Peek(1) == 0x4 && st'.Peek(2) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff && st'.Peek(3) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 9 ==> ((st'.Peek(7) == 0x229))
	requires st'.Operands() == 13 ==> ((st'.Peek(7) == 0xbdb && st'.Peek(8) == 0x0 && st'.Peek(11) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x00,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x20,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|0x04,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x04,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
    assert st.Operands() in {9,13};
    assert st.Peek(2) == st'.Peek(2) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
    assert st.Peek(3) == st'.Peek(3) == 0x00;
    assert st.Operands() == 13 ==> st.Peek(8) == 0x00;
		st := Dup(st,2);
		// |fp=0x0060|0x20,0x04,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x04,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
    assert st.Operands() in {9,13};    
		// |fp=0x0060|0x20,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		st := block_0_0x0773(st);
		return st;
	}

	method block_0_0x0773(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0773
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {9,13}
	// Static stack items
	requires (st'.Peek(0) == 0x0 && st'.Peek(1) == 0x40 && st'.Peek(2) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff && st'.Peek(3) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 9 ==> ((st'.Peek(7) == 0x229))
	requires st'.Operands() == 13 ==> ((st'.Peek(7) == 0xbdb && st'.Peek(8) == 0x0 && st'.Peek(11) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x00,0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Keccak256(st);
		// |fp=0x0060|_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Caller(st);
		// |fp=0x0060|_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := AndU160(st);
    assert st.Operands() in {10,14};
    assert st.Peek(1) == st'.Peek(0) == 0x00;
		// |fp=0x0060|_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		st := block_0_0x07a4(st);
		return st;
	}

	method block_0_0x07a4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07a4
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {11,15}
	// Static stack items
	requires (st'.Peek(0) == 0x0 && st'.Peek(2) == 0x0 && st'.Peek(4) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff && st'.Peek(5) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 11 ==> ((st'.Peek(9) == 0x229))
	requires st'.Operands() == 15 ==> ((st'.Peek(9) == 0xbdb && st'.Peek(10) == 0x0 && st'.Peek(13) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x00,_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x00,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
    assert st.Operands() in {14,10};
    assert st.Peek(3) == st'.Peek(4) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
    assert st.Operands() == 14 ==> st.Peek(9) == st'.Peek(10) == 0x00;            
		st := Add(st);
		// |fp=0x0060|0x20,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|_,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
    assert st.Operands() in {13,9};
    assert st.Peek(2) == st'.Peek(4) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
    assert st.Operands() == 13 ==> st.Peek(8) == st'.Peek(10) == 0x00;    
		st := Dup(st,2);
		// |fp=0x0060|0x20,_,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := MStore(st);
    assert st.Operands() in {12,8};
    assert st.Peek(1) == st'.Peek(4) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
    assert st.Operands() == 12 ==> st.Peek(7) == st'.Peek(10) == 0x00;
		// |fp=0x0060|0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Add(st);
		st := block_0_0x07ae(st);
		return st;
	}

	method block_0_0x07ae(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07ae
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {8,12}
	// Static stack items
	requires (st'.Peek(0) == 0x40 && st'.Peek(1) == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff && st'.Peek(2) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 8 ==> ((st'.Peek(6) == 0x229))
	requires st'.Operands() == 12 ==> ((st'.Peek(6) == 0xbdb && st'.Peek(7) == 0x0 && st'.Peek(10) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Keccak256(st);
		// |fp=0x0060|_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := SLoad(st);
		// |fp=0x0060|_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x00,_,_,_,0x229,_|
		st := Eq(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := block_0_0x07b4(st);
		return st;
	}

	method block_0_0x07b4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07b4
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {7,11}
	// Static stack items
	requires (st'.Peek(1) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 7 ==> ((st'.Peek(5) == 0x229))
	requires st'.Operands() == 11 ==> ((st'.Peek(5) == 0xbdb && st'.Peek(6) == 0x0 && st'.Peek(9) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := JumpDest(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Push2(st,0x08cf);
		// |fp=0x0060|0x8cf,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x8cf,_,0x00,_,_,_,0x229,_|
		assume st.IsJumpDest(0x8cf);
		st := JumpI(st);
		if st.PC() == 0x8cf { st := block_0_0x08cf(st); return st;}
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x04);
		// |fp=0x0060|0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x04,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := Dup(st,7);
		st := block_0_0x07c0(st);
		return st;
	}

	method block_0_0x07c0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07c0
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {10,14}
	// Static stack items
	requires (st'.Peek(1) == 0x0 && st'.Peek(2) == 0x4 && st'.Peek(4) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 10 ==> ((st'.Peek(8) == 0x229))
	requires st'.Operands() == 14 ==> ((st'.Peek(8) == 0xbdb && st'.Peek(9) == 0x0 && st'.Peek(12) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x00,_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		st := block_0_0x07f1(st);
		return st;
	}

	method block_0_0x07f1(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07f1
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {9,13}
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x4 && st'.Peek(3) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 9 ==> ((st'.Peek(7) == 0x229))
	requires st'.Operands() == 13 ==> ((st'.Peek(7) == 0xbdb && st'.Peek(8) == 0x0 && st'.Peek(11) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x20,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x04,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|0x04,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x04,0x20,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x20,0x04,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x04,0x20,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0x229,_|
		st := Keccak256(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		st := block_0_0x07fc(st);
		return st;
	}

	method block_0_0x07fc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07fc
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {9,13}
	// Static stack items
	requires (st'.Peek(0) == 0x0 && st'.Peek(3) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 9 ==> ((st'.Peek(7) == 0x229))
	requires st'.Operands() == 13 ==> ((st'.Peek(7) == 0xbdb && st'.Peek(8) == 0x0 && st'.Peek(11) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Caller(st);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x00,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		st := block_0_0x082d(st);
		return st;
	}

	method block_0_0x082d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x082d
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {10,14}
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x0 && st'.Peek(4) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 10 ==> ((st'.Peek(8) == 0x229))
	requires st'.Operands() == 14 ==> ((st'.Peek(8) == 0xbdb && st'.Peek(9) == 0x0 && st'.Peek(12) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x20,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x20,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|_,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x20,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x20,_,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x20,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0x229,_|
		st := Keccak256(st);
		st := block_0_0x0837(st);
		return st;
	}

	method block_0_0x0837(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0837
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {8,12}
	// Static stack items
	requires (st'.Peek(2) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 8 ==> ((st'.Peek(6) == 0x229))
	requires st'.Operands() == 12 ==> ((st'.Peek(6) == 0xbdb && st'.Peek(7) == 0x0 && st'.Peek(10) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := SLoad(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Lt(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := IsZero(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Push2(st,0x0844);
		// |fp=0x0060|0x844,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x844,_,0x00,_,_,_,0x229,_|
		assume st.IsJumpDest(0x844);
		st := JumpI(st);
		if st.PC() == 0x844 { st := block_0_0x0844(st); return st;}
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		st := block_0_0x0842(st);
		return st;
	}

	method block_0_0x0842(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0842
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {7,11}
	// Static stack items
	requires (st'.Peek(0) == 0x0 && st'.Peek(1) == 0x0)
	// Dynamic stack items
	// requires st'.Operands() == 7 ==> ((st'.Peek(5) == 0x229))
	// requires st'.Operands() == 11 ==> ((st'.Peek(5) == 0xbdb && st'.Peek(6) == 0x0 && st'.Peek(9) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x00,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x00,_,_,_,0x229,_|
		st := Dup(st,1);
		// |fp=0x0060|0x00,0x00,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x00,0x00,_,_,_,0x229,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x0844(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0844
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {6,10}
	// Static stack items
	requires (st'.Peek(0) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 6 ==> ((st'.Peek(4) == 0x229))
	requires st'.Operands() == 10 ==> ((st'.Peek(4) == 0xbdb && st'.Peek(5) == 0x0 && st'.Peek(8) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := JumpDest(st);
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x04);
		// |fp=0x0060|0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x04,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := Dup(st,7);
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		st := block_0_0x0876(st);
		return st;
	}

	method block_0_0x0876(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0876
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {11,15}
	// Static stack items
	requires (st'.Peek(0) == 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x4 && st'.Peek(5) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 11 ==> ((st'.Peek(9) == 0x229))
	requires st'.Operands() == 15 ==> ((st'.Peek(9) == 0xbdb && st'.Peek(10) == 0x0 && st'.Peek(13) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x00,_,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x00,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x00,0x04,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x20,0x04,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x04,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|0x04,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x04,0x20,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x20,0x04,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x04,0x20,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		st := block_0_0x087f(st);
		return st;
	}

	method block_0_0x087f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x087f
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {8,12}
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(2) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 8 ==> ((st'.Peek(6) == 0x229))
	requires st'.Operands() == 12 ==> ((st'.Peek(6) == 0xbdb && st'.Peek(7) == 0x0 && st'.Peek(10) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0x229,_|
		st := Keccak256(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Caller(st);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		st := block_0_0x089e(st);
		return st;
	}

	method block_0_0x089e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x089e
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {10,14}
	// Static stack items
	requires (st'.Peek(1) == 0x0 && st'.Peek(4) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 10 ==> ((st'.Peek(8) == 0x229))
	requires st'.Operands() == 14 ==> ((st'.Peek(8) == 0xbdb && st'.Peek(9) == 0x0 && st'.Peek(12) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x00,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x20,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|_,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x20,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		st := block_0_0x08bb(st);
		return st;
	}

	method block_0_0x08bb(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08bb
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {10,14}
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(2) == 0x20 && st'.Peek(4) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 10 ==> ((st'.Peek(8) == 0x229))
	requires st'.Operands() == 14 ==> ((st'.Peek(8) == 0xbdb && st'.Peek(9) == 0x0 && st'.Peek(12) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x20,_,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x20,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0x229,_|
		st := Keccak256(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,3);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,3);
		st := block_0_0x08c6(st);
		return st;
	}

	method block_0_0x08c6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08c6
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {11,15}
	// Static stack items
	requires (st'.Peek(2) == 0x0 && st'.Peek(5) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 11 ==> ((st'.Peek(9) == 0x229))
	requires st'.Operands() == 15 ==> ((st'.Peek(9) == 0xbdb && st'.Peek(10) == 0x0 && st'.Peek(13) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := SLoad(st);
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Sub(st);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,3);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|_,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|_,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,_,0x00,_,_,_,0x229,_|
		st := SStore(st);
		st := block_0_0x08ce(st);
		return st;
	}

	method block_0_0x08ce(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08ce
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {7,11}
	// Static stack items
	requires (st'.Peek(1) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 7 ==> ((st'.Peek(5) == 0x229))
	requires st'.Operands() == 11 ==> ((st'.Peek(5) == 0xbdb && st'.Peek(6) == 0x0 && st'.Peek(9) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := block_0_0x08cf(st);
		return st;
	}

	method block_0_0x08cf(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08cf
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {6,10}
	// Static stack items
	requires (st'.Peek(0) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 6 ==> ((st'.Peek(4) == 0x229))
	requires st'.Operands() == 10 ==> ((st'.Peek(4) == 0xbdb && st'.Peek(5) == 0x0 && st'.Peek(8) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := JumpDest(st);
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x03);
		// |fp=0x0060|0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x03,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Dup(st,7);
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		st := block_0_0x0901(st);
		return st;
	}

	method block_0_0x0901(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0901
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {11,15}
	// Static stack items
	requires (st'.Peek(0) == 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x3 && st'.Peek(5) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 11 ==> ((st'.Peek(9) == 0x229))
	requires st'.Operands() == 15 ==> ((st'.Peek(9) == 0xbdb && st'.Peek(10) == 0x0 && st'.Peek(13) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x00,_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x20,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x03,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|0x03,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x03,0x20,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x20,0x03,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x03,0x20,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		st := block_0_0x090a(st);
		return st;
	}

	method block_0_0x090a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x090a
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {8,12}
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(2) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 8 ==> ((st'.Peek(6) == 0x229))
	requires st'.Operands() == 12 ==> ((st'.Peek(6) == 0xbdb && st'.Peek(7) == 0x0 && st'.Peek(10) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0x229,_|
		st := Keccak256(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,3);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,3);
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := SLoad(st);
		st := block_0_0x0915(st);
		return st;
	}

	method block_0_0x0915(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0915
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {11,15}
	// Static stack items
	requires (st'.Peek(2) == 0x0 && st'.Peek(5) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 11 ==> ((st'.Peek(9) == 0x229))
	requires st'.Operands() == 15 ==> ((st'.Peek(9) == 0xbdb && st'.Peek(10) == 0x0 && st'.Peek(13) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Sub(st);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,3);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|_,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|_,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,_,0x00,_,_,_,0x229,_|
		st := SStore(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		st := block_0_0x091d(st);
		return st;
	}

	method block_0_0x091d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x091d
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {6,10}
	// Static stack items
	requires (st'.Peek(0) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 6 ==> ((st'.Peek(4) == 0x229))
	requires st'.Operands() == 10 ==> ((st'.Peek(4) == 0xbdb && st'.Peek(5) == 0x0 && st'.Peek(8) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x03);
		// |fp=0x0060|0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x03,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Dup(st,6);
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		st := block_0_0x094f(st);
		return st;
	}

	method block_0_0x094f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x094f
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {10,14}
	// Static stack items
	requires (st'.Peek(1) == 0x0 && st'.Peek(2) == 0x3 && st'.Peek(4) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 10 ==> ((st'.Peek(8) == 0x229))
	requires st'.Operands() == 14 ==> ((st'.Peek(8) == 0xbdb && st'.Peek(9) == 0x0 && st'.Peek(12) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x00,_,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x00,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x00,0x03,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x20,0x03,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x03,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|0x03,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x03,0x20,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x20,0x03,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x03,0x20,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		st := block_0_0x0959(st);
		return st;
	}

	method block_0_0x0959(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0959
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {9,13}
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x20 && st'.Peek(3) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 9 ==> ((st'.Peek(7) == 0x229))
	requires st'.Operands() == 13 ==> ((st'.Peek(7) == 0xbdb && st'.Peek(8) == 0x0 && st'.Peek(11) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x20,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x40,_,0x00,_,_,_,0x229,_|
		st := Keccak256(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x00);
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,3);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,3);
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := SLoad(st);
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		st := block_0_0x0963(st);
		return st;
	}

	method block_0_0x0963(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0963
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {10,14}
	// Static stack items
	requires (st'.Peek(1) == 0x0 && st'.Peek(4) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 10 ==> ((st'.Peek(8) == 0x229))
	requires st'.Operands() == 14 ==> ((st'.Peek(8) == 0xbdb && st'.Peek(9) == 0x0 && st'.Peek(12) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,3);
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|_,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|_,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,_,0x00,_,_,_,0x229,_|
		st := SStore(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Dup(st,3);
		st := block_0_0x096b(st);
		return st;
	}

	method block_0_0x096b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x096b
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {7,11}
	// Static stack items
	requires (st'.Peek(1) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 7 ==> ((st'.Peek(5) == 0x229))
	requires st'.Operands() == 11 ==> ((st'.Peek(5) == 0xbdb && st'.Peek(6) == 0x0 && st'.Peek(9) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x00,_,_,_,0x229,_|
		st := Dup(st,5);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,_,0x00,_,_,_,0x229,_|
		st := AndU160(st);
		// |fp=0x0060|_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x00,_,_,_,0x229,_|
		st := PushN(st,32,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
		// |fp=0x0060|0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,5);
		// |fp=0x0060|_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x40);
		st := block_0_0x09bc(st);
		return st;
	}

	method block_0_0x09bc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09bc
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {11,15}
	// Static stack items
	requires (st'.Peek(0) == 0x40 && st'.Peek(2) == 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef && st'.Peek(5) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 11 ==> ((st'.Peek(9) == 0x229))
	requires st'.Operands() == 15 ==> ((st'.Peek(9) == 0xbdb && st'.Peek(10) == 0x0 && st'.Peek(13) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x40,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := MLoad(st);
		// |fp=0x0060|0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,1);
		// |fp=0x0060|0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,3);
		// |fp=0x0060|_,0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,2);
		// |fp=0x0060|0x60,_,0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x60,_,0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := MStore(st);
		// |fp=0x0060|0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x60,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Add(st);
		// |fp=0x0060|0x80,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x80,0x60,_,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,2);
		st := block_0_0x09c5(st);
		return st;
	}

	method block_0_0x09c5(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09c5
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {12,16}
	// Static stack items
	requires (st'.Peek(1) == 0x60 && st'.Peek(2) == 0x80 && st'.Peek(3) == 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef && st'.Peek(6) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 12 ==> ((st'.Peek(10) == 0x229))
	requires st'.Operands() == 16 ==> ((st'.Peek(10) == 0xbdb && st'.Peek(11) == 0x0 && st'.Peek(14) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x40,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := MLoad(st);
		// |fp=0x0060|0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Dup(st,1);
		// |fp=0x0060|0x60,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x60,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,2);
		// |fp=0x0060|0x80,0x60,0x60,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x80,0x60,0x60,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Sub(st);
		// |fp=0x0060|0x20,0x60,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x20,0x60,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		st := block_0_0x09ce(st);
		return st;
	}

	method block_0_0x09ce(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09ce
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {11,15}
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(1) == 0x20 && st'.Peek(2) == 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef && st'.Peek(5) == 0x0)
	// Dynamic stack items
	requires st'.Operands() == 11 ==> ((st'.Peek(9) == 0x229))
	requires st'.Operands() == 15 ==> ((st'.Peek(9) == 0xbdb && st'.Peek(10) == 0x0 && st'.Peek(13) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|0x60,0x20,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x60,0x20,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,_,_,0x00,_,_,_,0x229,_|
		st := LogN(st,3);
		// |fp=0x0060|0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,_,_,_,0x229,_|
		st := Push1(st,0x01);
		// |fp=0x0060|0x01,0x00,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x01,0x00,_,_,_,0x229,_|
		st := Swap(st,1);
		// |fp=0x0060|0x00,0x01,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x00,0x01,_,_,_,0x229,_|
		st := Pop(st);
		// |fp=0x0060|0x01,_,_,_,0xbdb,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x01,_,_,_,0x229,_|
		st := Swap(st,4);
		// |fp=0x0060|0xbdb,_,_,_,0x01,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x229,_,_,_,0x01,_|
		st := Swap(st,3);
		// |fp=0x0060|_,_,_,0xbdb,0x01,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,_,0x229,0x01,_|
		st := Pop(st);
		// |fp=0x0060|_,_,0xbdb,0x01,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,_,0x229,0x01,_|
		st := Pop(st);
		st := block_0_0x09d7(st);
		return st;
	}

	method block_0_0x09d7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09d7
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() in {4,8}
	// Static stack items
	requires (st'.Peek(2) == 0x1)
	// Dynamic stack items
	requires st'.Operands() == 4 ==> ((st'.Peek(1) == 0x229))
	requires st'.Operands() == 8 ==> ((st'.Peek(1) == 0xbdb && st'.Peek(3) == 0x0 && st'.Peek(6) == 0x3b0))
	{
		var st := st';
		// |fp=0x0060|_,0xbdb,0x01,0x00,_,_,0x3b0,_|
		// |fp=0x0060|_,0x229,0x01,_|
		st := Pop(st);
		// |fp=0x0060|0xbdb,0x01,0x00,_,_,0x3b0,_|
		// |fp=0x0060|0x229,0x01,_|
		assume st.IsJumpDest(0x229);
		assume st.IsJumpDest(0xbdb);
		st := Jump(st);
		match st.PC() {
			case 0x229 => { st := block_0_0x0229(st); }
			case 0xbdb => { st := block_0_0x0bdb(st); }
	}
		return st;
	}

	method block_0_0x0bdb(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bdb
	// Free memory pointer
	requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x1 && st'.Peek(1) == 0x0 && st'.Peek(4) == 0x3b0)
	{
		var st := st';
		// |fp=0x0060|0x01,0x00,_,_,0x3b0,_|
		st := JumpDest(st);
		// |fp=0x0060|0x01,0x00,_,_,0x3b0,_|
		st := Swap(st,1);
		// |fp=0x0060|0x00,0x01,_,_,0x3b0,_|
		st := Pop(st);
		// |fp=0x0060|0x01,_,_,0x3b0,_|
		st := Swap(st,3);
		// |fp=0x0060|0x3b0,_,_,0x01,_|
		st := Swap(st,2);
		// |fp=0x0060|_,_,0x3b0,0x01,_|
		st := Pop(st);
		// |fp=0x0060|_,0x3b0,0x01,_|
		st := Pop(st);
		// |fp=0x0060|0x3b0,0x01,_|
		assume st.IsJumpDest(0x3b0);
		st := Jump(st);
		st := block_0_0x03b0(st);
		return st;
	}

}
