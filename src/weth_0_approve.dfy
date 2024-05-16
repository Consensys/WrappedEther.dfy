include "../../evm-dafny/src/dafny/evm.dfy"
include "../../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module approve {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x0147(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0147
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
		st := Push2(st,0x0152);
		//|fp=0x0060|0x152*,_,_|
		assume st.IsJumpDest(0x152);
		st := JumpI(st);
		if st.PC() == 0x152 { st := block_0_0x0152(st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|_,_|
		st := Dup(st,1);
		//|fp=0x0060|_,_,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x0152(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0152
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x0187);
		//|fp=0x0060|0x187*,_|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04*,0x187*,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04*,_,0x187*,_|
		st := Dup(st,1);
		//|fp=0x0060|_,0x04*,_,0x187*,_|
		st := CallDataLoad(st);
		//|fp=0x0060|_,0x04*,_,0x187*,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|_,_,0x04*,_,0x187*,_|
		st := And(st);
		st := block_0_0x0171(st);
		return st;
	}

	method block_0_0x0171(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0171
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(1) == 0x4 && st'.Peek(3) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,0x04*,_,0x187*,_|
		st := Swap(st,1);
		//|fp=0x0060|0x04*,_,_,0x187*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,0x04*,_,_,0x187*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20*,0x04*,_,_,0x187*,_|
		st := Add(st);
		//|fp=0x0060|0x24*,_,_,0x187*,_|
		st := Swap(st,1);
		//|fp=0x0060|_,0x24*,_,0x187*,_|
		st := Swap(st,2);
		//|fp=0x0060|_,0x24*,_,0x187*,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24*,_,_,0x187*,_|
		st := Dup(st,1);
		//|fp=0x0060|_,0x24*,_,_,0x187*,_|
		st := CallDataLoad(st);
		st := block_0_0x017a(st);
		return st;
	}

	method block_0_0x017a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x017a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(1) == 0x24 && st'.Peek(4) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,0x24*,_,_,0x187*,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24*,_,_,_,0x187*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,0x24*,_,_,_,0x187*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|_,_,_,_,_,0x187*,_|
		st := Add(st);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := Swap(st,2);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := Pop(st);
		//|fp=0x0060|_,_,_,0x187*,_|
		st := Pop(st);
		st := block_0_0x0183(st);
		return st;
	}

	method block_0_0x0183(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0183
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,_,0x187*,_|
		st := Push2(st,0x057b);
		//|fp=0x0060|0x57b*,_,_,0x187*,_|
		assume st.IsJumpDest(0x57b);
		st := Jump(st);
		st := block_0_0x057b(st);
		return st;
	}

	method block_0_0x0187(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0187
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	{
		var st := st';
		//|fp=0x0060|_,_|
		st := JumpDest(st);
		//|fp=0x0060|_,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40*,_,_|
		st := MLoad(st);
		//|fp=0x0060|0x60*,_,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60*,_,_,_|
		st := Dup(st,3);
		//|fp=0x0060|_,0x60*,_,_,_|
		st := IsZero(st);
		//|fp=0x0060|_,0x60*,_,_,_|
		st := IsZero(st);
		//|fp=0x0060|_,0x60*,_,_,_|
		st := IsZero(st);
		st := block_0_0x0190(st);
		return st;
	}

	method block_0_0x0190(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0190
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(1) == 0x60)
	{
		var st := st';
		//|fp=0x0060|_,0x60*,_,_,_|
		st := IsZero(st);
		//|fp=0x0060|_,0x60*,_,_,_|
		st := Dup(st,2);
		//|fp=0x0060|_,_,0x60*,_,_,_|
		st := MStore(st);
		//|fp=0x0060|0x60*,_,_,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,0x60*,_,_,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20*,0x60*,_,_,_|
		st := Add(st);
		//|fp=0x0060|0x80*,_,_,_|
		st := Swap(st,2);
		//|fp=0x0060|_,_,0x80*,_|
		st := Pop(st);
		//|fp=0x0060|_,0x80*,_|
		st := Pop(st);
		st := block_0_0x0199(st);
		return st;
	}

	method block_0_0x0199(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0199
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires (st'.Peek(0) == 0x80)
	{
		var st := st';
		//|fp=0x0060|0x80*,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40*,0x80*,_|
		st := MLoad(st);
		//|fp=0x0060|0x60*,0x80*,_|
		st := Dup(st,1);
		//|fp=0x0060|_,0x60*,0x80*,_|
		st := Swap(st,2);
		//|fp=0x0060|0x80*,0x60*,_,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|_,_,_,_|
		st := Sub(st);
		//|fp=0x0060|_,_,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,_|
		st := Return(st);
		return st;
	}

	method block_0_0x057b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x057b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,_,0x187*,_|
		st := JumpDest(st);
		//|fp=0x0060|_,_,0x187*,_|
		st := Push1(st,0x00);
		//|fp=0x0060|_,_,_,0x187*,_|
		st := Dup(st,2);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := Push1(st,0x04);
		//|fp=0x0060|_,_,_,_,_,0x187*,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00*,_,_,_,_,_,0x187*,_|
		st := Caller(st);
		//|fp=0x0060|_,0x00*,_,_,_,_,_,0x187*,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|_,_,0x00*,_,_,_,_,_,0x187*,_|
		st := And(st);
		st := block_0_0x059a(st);
		return st;
	}

	method block_0_0x059a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x059a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(1) == 0x0 && st'.Peek(7) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,0x00*,_,_,_,_,_,0x187*,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|_,_,0x00*,_,_,_,_,_,0x187*,_|
		st := And(st);
		//|fp=0x0060|_,0x00*,_,_,_,_,_,0x187*,_|
		st := Dup(st,2);
		//|fp=0x0060|_,_,0x00*,_,_,_,_,_,0x187*,_|
		st := MStore(st);
		//|fp=0x0060|0x00*,_,_,_,_,_,0x187*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,0x00*,_,_,_,_,_,0x187*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20*,0x00*,_,_,_,_,_,0x187*,_|
		st := Add(st);
		//|fp=0x0060|0x20*,_,_,_,_,_,0x187*,_|
		st := Swap(st,1);
		//|fp=0x0060|_,0x20*,_,_,_,_,0x187*,_|
		st := Dup(st,2);
		st := block_0_0x05b7(st);
		return st;
	}

	method block_0_0x05b7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05b7
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires (st'.Peek(2) == 0x20 && st'.Peek(7) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,_,0x20*,_,_,_,_,0x187*,_|
		st := MStore(st);
		//|fp=0x0060|0x20*,_,_,_,_,0x187*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,0x20*,_,_,_,_,0x187*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|_,_,_,_,_,_,0x187*,_|
		st := Add(st);
		//|fp=0x0060|_,_,_,_,_,0x187*,_|
		st := Push1(st,0x00);
		//|fp=0x0060|_,_,_,_,_,_,0x187*,_|
		st := Keccak256(st);
		//|fp=0x0060|_,_,_,_,_,0x187*,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00*,_,_,_,_,_,0x187*,_|
		st := Dup(st,6);
		//|fp=0x0060|_,0x00*,_,_,_,_,_,0x187*,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		st := block_0_0x05d6(st);
		return st;
	}

	method block_0_0x05d6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05d6
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires (st'.Peek(2) == 0x0 && st'.Peek(8) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,_,0x00*,_,_,_,_,_,0x187*,_|
		st := And(st);
		//|fp=0x0060|_,0x00*,_,_,_,_,_,0x187*,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|_,_,0x00*,_,_,_,_,_,0x187*,_|
		st := And(st);
		//|fp=0x0060|_,0x00*,_,_,_,_,_,0x187*,_|
		st := Dup(st,2);
		//|fp=0x0060|_,_,0x00*,_,_,_,_,_,0x187*,_|
		st := MStore(st);
		//|fp=0x0060|0x00*,_,_,_,_,_,0x187*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,0x00*,_,_,_,_,_,0x187*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20*,0x00*,_,_,_,_,_,0x187*,_|
		st := Add(st);
		//|fp=0x0060|0x20*,_,_,_,_,_,0x187*,_|
		st := Swap(st,1);
		st := block_0_0x05f3(st);
		return st;
	}

	method block_0_0x05f3(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05f3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(1) == 0x20 && st'.Peek(6) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,0x20*,_,_,_,_,0x187*,_|
		st := Dup(st,2);
		//|fp=0x0060|_,_,0x20*,_,_,_,_,0x187*,_|
		st := MStore(st);
		//|fp=0x0060|0x20*,_,_,_,_,0x187*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,0x20*,_,_,_,_,0x187*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|_,_,_,_,_,_,0x187*,_|
		st := Add(st);
		//|fp=0x0060|_,_,_,_,_,0x187*,_|
		st := Push1(st,0x00);
		//|fp=0x0060|_,_,_,_,_,_,0x187*,_|
		st := Keccak256(st);
		//|fp=0x0060|_,_,_,_,_,0x187*,_|
		st := Dup(st,2);
		//|fp=0x0060|_,_,_,_,_,_,0x187*,_|
		st := Swap(st,1);
		st := block_0_0x05fd(st);
		return st;
	}

	method block_0_0x05fd(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05fd
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(6) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,_,_,_,_,_,0x187*,_|
		st := SStore(st);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := Pop(st);
		//|fp=0x0060|_,_,_,0x187*,_|
		st := Dup(st,3);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|_,_,_,_,_,0x187*,_|
		st := And(st);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := Caller(st);
		//|fp=0x0060|_,_,_,_,_,0x187*,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|_,_,_,_,_,_,0x187*,_|
		st := And(st);
		st := block_0_0x062d(st);
		return st;
	}

	method block_0_0x062d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x062d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(5) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,_,_,_,_,0x187*,_|
		st := PushN(st,32,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
		//|fp=0x0060|_,_,_,_,_,_,0x187*,_|
		st := Dup(st,5);
		//|fp=0x0060|_,_,_,_,_,_,_,0x187*,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40*,_,_,_,_,_,_,_,0x187*,_|
		st := MLoad(st);
		//|fp=0x0060|0x60*,_,_,_,_,_,_,_,0x187*,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60*,_,_,_,_,_,_,_,_,0x187*,_|
		st := Dup(st,3);
		//|fp=0x0060|_,0x60*,_,_,_,_,_,_,_,_,0x187*,_|
		st := Dup(st,2);
		//|fp=0x0060|_,_,0x60*,_,_,_,_,_,_,_,_,0x187*,_|
		st := MStore(st);
		st := block_0_0x0656(st);
		return st;
	}

	method block_0_0x0656(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0656
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(9) == 0x187)
	{
		var st := st';
		//|fp=0x0060|0x60*,_,_,_,_,_,_,_,_,0x187*,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20*,0x60*,_,_,_,_,_,_,_,_,0x187*,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20*,0x60*,_,_,_,_,_,_,_,_,0x187*,_|
		st := Add(st);
		//|fp=0x0060|0x80*,_,_,_,_,_,_,_,_,0x187*,_|
		st := Swap(st,2);
		//|fp=0x0060|_,_,0x80*,_,_,_,_,_,_,0x187*,_|
		st := Pop(st);
		//|fp=0x0060|_,0x80*,_,_,_,_,_,_,0x187*,_|
		st := Pop(st);
		//|fp=0x0060|0x80*,_,_,_,_,_,_,0x187*,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40*,0x80*,_,_,_,_,_,_,0x187*,_|
		st := MLoad(st);
		//|fp=0x0060|0x60*,0x80*,_,_,_,_,_,_,0x187*,_|
		st := Dup(st,1);
		st := block_0_0x0660(st);
		return st;
	}

	method block_0_0x0660(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0660
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires (st'.Peek(1) == 0x60 && st'.Peek(2) == 0x80 && st'.Peek(9) == 0x187)
	{
		var st := st';
		//|fp=0x0060|_,0x60*,0x80*,_,_,_,_,_,_,0x187*,_|
		st := Swap(st,2);
		//|fp=0x0060|0x80*,0x60*,_,_,_,_,_,_,_,0x187*,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|_,_,_,_,_,_,_,_,_,0x187*,_|
		st := Sub(st);
		//|fp=0x0060|_,_,_,_,_,_,_,_,0x187*,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,_,_,_,_,_,_,0x187*,_|
		st := LogN(st,3);
		//|fp=0x0060|_,_,_,0x187*,_|
		st := Push1(st,0x01);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := Swap(st,1);
		//|fp=0x0060|_,_,_,_,0x187*,_|
		st := Pop(st);
		//|fp=0x0060|_,_,_,0x187*,_|
		st := Swap(st,3);
		st := block_0_0x0669(st);
		return st;
	}

	method block_0_0x0669(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0669
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == 0x187)
	{
		var st := st';
		//|fp=0x0060|0x187*,_,_,_,_|
		st := Swap(st,2);
		//|fp=0x0060|_,_,0x187*,_,_|
		st := Pop(st);
		//|fp=0x0060|_,0x187*,_,_|
		st := Pop(st);
		//|fp=0x0060|0x187*,_,_|
		assume st.IsJumpDest(0x187);
		st := Jump(st);
		st := block_0_0x0187(st);
		return st;
	}

}
