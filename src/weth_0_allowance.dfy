include "../../evm-dafny/src/dafny/evm.dfy"
include "../../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module allowance {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x03d4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03d4
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
		st := Push2(st,0x03df);
		//|fp=0x0060|0x3df,_,_|
		assume st.IsJumpDest(0x3df);
		st := JumpI(st);
		if st.PC() == 0x3df { st := block_0_0x03df(st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x03df(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03df
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x042a);
		//|fp=0x0060|0x42a,_|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,0x42a,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x42a,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x04,0x42a,_|
		st := CallDataLoad(st);
		//|fp=0x0060|_,0x04,0x04,0x42a,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x04,0x04,0x42a,_|
		st := AndU160(st);
		st := block_0_0x03fe(st);
		return st;
	}

	method block_0_0x03fe(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03fe
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(1) == 0x4 && st'.Peek(3) == 0x42a)
	{
		var st := st';
		//|fp=0x0060|_,0x04,0x04,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|0x04,_,0x04,0x42a,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,_,0x04,0x42a,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,0x04,_,0x04,0x42a,_|
		st := Add(st);
		//|fp=0x0060|0x24,_,0x04,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|_,0x24,0x04,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,_,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,_,0x42a,_|
		st := Dup(st,1);
		//|fp=0x0060|0x24,0x24,0x04,_,0x42a,_|
		st := CallDataLoad(st);
		st := block_0_0x0407(st);
		return st;
	}

	method block_0_0x0407(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0407
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(1) == 0x24 && st'.Peek(4) == 0x42a)
	{
		var st := st';
		//|fp=0x0060|_,0x24,0x04,_,0x42a,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x24,0x04,_,0x42a,_|
		st := AndU160(st);
		//|fp=0x0060|_,0x24,0x04,_,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24,_,0x04,_,0x42a,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x24,_,0x04,_,0x42a,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,0x24,_,0x04,_,0x42a,_|
		st := Add(st);
		//|fp=0x0060|0x44,_,0x04,_,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|_,0x44,0x04,_,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x44,_,_,0x42a,_|
		st := Swap(st,1);
		st := block_0_0x0424(st);
		return st;
	}

	method block_0_0x0424(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0424
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(4) == 0x42a)
	{
		var st := st';
		//|fp=0x0060|0x44,0x04,_,_,0x42a,_|
		st := Pop(st);
		//|fp=0x0060|0x04,_,_,0x42a,_|
		st := Pop(st);
		//|fp=0x0060|_,_,0x42a,_|
		st := Push2(st,0x0be3);
		//|fp=0x0060|0xbe3,_,_,0x42a,_|
		assume st.IsJumpDest(0xbe3);
		st := Jump(st);
		st := block_0_0x0be3(st);
		return st;
	}

	method block_0_0x042a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x042a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	{
		var st := st';
		//|fp=0x0060|_,0x42a,_|
		st := JumpDest(st);
		//|fp=0x0060|_,0x42a,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,_,0x42a,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,_,0x42a,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,_,0x42a,_|
		st := Dup(st,3);
		//|fp=0x0060|_,0x60,0x60,_,0x42a,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,_,0x60,0x60,_,0x42a,_|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,_,0x42a,_|
		st := Push1(st,0x20);
		st := block_0_0x0434(st);
		return st;
	}

	method block_0_0x0434(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0434
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x60)
	{
		var st := st';
		//|fp=0x0060|0x20,0x60,0x60,_,0x42a,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,0x60,0x60,_,0x42a,_|
		st := Add(st);
		//|fp=0x0060|0x80,0x60,_,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|_,0x60,0x80,0x42a,_|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0x42a,_|
		st := Pop(st);
		//|fp=0x0060|0x80,0x42a,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0x42a,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0x42a,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0x42a,_|
		st := Swap(st,2);
		st := block_0_0x043d(st);
		return st;
	}

	method block_0_0x043d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x043d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == 0x80 && st'.Peek(1) == 0x60)
	{
		var st := st';
		//|fp=0x0060|0x80,0x60,0x60,0x42a,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,0x42a,_|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0x42a,_|
		st := Return(st);
		return st;
	}

	method block_0_0x0be3(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0be3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x42a)
	{
		var st := st';
		//|fp=0x0060|_,_,0x42a,_|
		st := JumpDest(st);
		//|fp=0x0060|_,_,0x42a,_|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,_,_,0x42a,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,_,_,0x42a,_|
		st := MStore(st);
		//|fp=0x0060|_,_,0x42a,_|
		st := Dup(st,2);
		//|fp=0x0060|_,_,_,0x42a,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_,_,_,0x42a,_|
		st := MStore(st);
		//|fp=0x0060|_,_,0x42a,_|
		st := Push1(st,0x40);
		st := block_0_0x0bef(st);
		return st;
	}

	method block_0_0x0bef(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bef
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(3) == 0x42a)
	{
		var st := st';
		//|fp=0x0060|0x40,_,_,0x42a,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,_,_,0x42a,_|
		st := Keccak256(st);
		//|fp=0x0060|_,_,_,0x42a,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,_,_,_,0x42a,_|
		st := MStore(st);
		//|fp=0x0060|_,_,0x42a,_|
		st := Dup(st,1);
		//|fp=0x0060|_,_,_,0x42a,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_,_,_,0x42a,_|
		st := MStore(st);
		//|fp=0x0060|_,_,0x42a,_|
		st := Push1(st,0x40);
		st := block_0_0x0bfb(st);
		return st;
	}

	method block_0_0x0bfb(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bfb
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(3) == 0x42a)
	{
		var st := st';
		//|fp=0x0060|0x40,_,_,0x42a,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,_,_,0x42a,_|
		st := Keccak256(st);
		//|fp=0x0060|_,_,_,0x42a,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_,_,_,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|_,_,0x00,_,0x42a,_|
		st := Pop(st);
		//|fp=0x0060|_,0x00,_,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|_,0x00,_,0x42a,_|
		st := Pop(st);
		//|fp=0x0060|0x00,_,0x42a,_|
		st := Pop(st);
		st := block_0_0x0c05(st);
		return st;
	}

	method block_0_0x0c05(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0c05
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x42a)
	{
		var st := st';
		//|fp=0x0060|_,0x42a,_|
		st := SLoad(st);
		//|fp=0x0060|_,0x42a,_|
		st := Dup(st,2);
		//|fp=0x0060|0x42a,_,0x42a,_|
		assume st.IsJumpDest(0x42a);
		st := Jump(st);
		st := block_0_0x042a(st);
		return st;
	}

}
