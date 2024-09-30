include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module approve {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header
	import opened Int

	method block_0_0x0147(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0147
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires st'.evm.stack.contents == [st'.Peek(0)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := CallValue(st);
		//|fp=0x0060|_,_|
		st := IsZero(st);
		//|fp=0x0060|_,_|
		st := Push2(st,0x0152);
		//|fp=0x0060|0x152,_,_|
		assume {:axiom} st.IsJumpDest(0x152);
		st := JumpI(st);
		if st.PC() == 0x152 { 
			stackLemma(st,st.Operands());
			st := block_0_0x0152(st); 
			return st;
		}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_|
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
	requires st'.evm.stack.contents == [st'.Peek(0)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x0187);
		//|fp=0x0060|0x187,_|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,0x187,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x187,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x04,0x187,_|
		st := CallDataLoad(st);
		//|fp=0x0060|callData[0x04],0x04,0x04,0x187,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,callData[0x04],0x04,0x04,0x187,_|
		st := AndU160(st);
		var guy := st.Peek(0) as u160;
		assert guy as u256 == st.evm.context.CallDataRead(0x04) % (Int.TWO_160 as u256) ;
		//|fp=0x0060|guy,0x04,0x04,0x187,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0171(guy,st);
		return st;
	}

	method block_0_0x0171(guy: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0171
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires st'.evm.stack.contents == [guy as u256,0x4,0x04,0x187,st'.Peek(4)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|guy,0x04,0x04,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|0x04,guy,0x04,0x187,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,guy,0x04,0x187,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		//|fp=0x0060|0x20,0x04,guy,0x04,0x187,_|
		st := Add(st);
		//|fp=0x0060|0x24,guy,0x04,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|guy,0x24,0x04,0x187,_|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,guy,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,guy,0x187,_|
		st := Dup(st,1);
		//|fp=0x0060|0x24,0x24,0x04,guy,0x187,_|
		st := CallDataLoad(st);
		//|fp=0x0060|wad,0x24,0x04,guy,0x187,_|
		var wad := st.Peek(0);
		assert wad == st.evm.context.CallDataRead(0x24) ;
		stackLemma(st,st.Operands());
		st := block_0_0x017a(guy,wad,st);
		return st;
	}

	method block_0_0x017a(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x017a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires st'.evm.stack.contents == [wad,0x24,0x04,guy as u256,0x187,st'.Peek(5)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,0x24,0x04,guy,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24,wad,0x04,guy,0x187,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x24,wad,0x04,guy,0x187,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x44,wad,0x04,guy,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|wad,0x44,0x04,guy,0x187,_|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x44,wad,guy,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|0x44,0x04,wad,guy,0x187,_|
		st := Pop(st);
		//|fp=0x0060|0x04,wad,guy,0x187,_|
		st := Pop(st);
		//|fp=0x0060|wad,guy,0x187,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0183(guy,wad,st);
		return st;
	}

	method block_0_0x0183(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0183
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires st'.evm.stack.contents == [wad,guy as u256,0x187,st'.Peek(3)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,guy,0x187,_|
		st := Push2(st,0x057b);
		//|fp=0x0060|0x57b,wad,guy,0x187,_|
		assume {:axiom} st.IsJumpDest(0x57b);
		st := Jump(st);
		stackLemma(st,st.Operands());
		st := block_0_0x057b(guy,wad,st);
		return st;
	}

	method 	block_0_0x0187(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0187
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires st'.evm.stack.contents == [0x1,st'.Peek(1)]
	// Storage
	requires st'.Load(Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04))) == wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x01,_|
		st := JumpDest(st);
		//|fp=0x0060|0x01,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x01,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x01,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x01,_|
		st := Dup(st,3);
		//|fp=0x0060|0x01,0x60,0x60,0x01,_|
		st := IsZero(st);
		//|fp=0x0060|0x00,0x60,0x60,0x01,_|
		st := IsZero(st);
		//|fp=0x0060|0x01,0x60,0x60,0x01,_|
		st := IsZero(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0190(guy,wad,st);
		return st;
	}

	method block_0_0x0190(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0190
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x60,0x60,0x1,st'.Peek(4)]
	// Storage
	requires st'.Load(Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04))) == wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x00,0x60,0x60,0x01,_|
		st := IsZero(st);
		//|fp=0x0060|0x01,0x60,0x60,0x01,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,0x01,0x60,0x60,0x01,_|
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0193(guy,wad,st);
		return st;
	}

	method block_0_0x0193(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0193
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60 && st'.Read(0x60) == 0x01
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires st'.evm.stack.contents == [0x60,0x60,0x01,st'.Peek(3)]
	// Storage
	requires st'.Load(Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04))) == wad
	{
		var st := st';
		stackLemma(st,st.Operands());	
		//|fp=0x0060|0x60,0x60,0x01,_| i.e st.Read(0x60) == 0x01
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,0x01,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		//|fp=0x0060|0x20,0x60,0x60,0x01,_|
		st := Add(st);
		//|fp=0x0060|0x80,0x60,0x01,_|
		st := Swap(st,2);
		//|fp=0x0060|0x01,0x60,0x80,_|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,_|
		st := Pop(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0199(guy,wad,st);
		return st;
	}

	method block_0_0x0199(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0199
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60 && st'.Read(0x60) == 0x01
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires st'.evm.stack.contents == [0x80,st'.Peek(1)]
	// Storage
	requires st'.Load(Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04))) == wad

	ensures st''.RETURNS? 
	ensures |st''.data| > 0 && st''.data[0] == 0x01 
	ensures st''.world.Exists(st'.evm.context.address)
	ensures st''.world.Read(st'.evm.context.address,Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04))) == wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x80,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,_|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,_|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,_|
		assert Int.ToBytes(st.Read(0x60) as nat)[0] == 0x01;
		//assume {:axiom} Memory.Slice(st.evm.memory, 0x60, 0x20) == Int.ToBytes(st.Read(0x60) as nat);
		MemoryReadAxiom(st,0x60);
		assert Memory.Slice(st.evm.memory, 0x60, 0x20)[0] == 0x01;
		st := Return(st);
		return st;
	}

	method block_0_0x057b(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x057b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires st'.evm.stack.contents == [wad,guy as u256,0x187,st'.Peek(3)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,guy,0x187,_|
		st := JumpDest(st);
		//|fp=0x0060|wad,guy,0x187,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,wad,guy,0x187,_|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x00,wad,guy,0x187,_|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,wad,0x00,wad,guy,0x187,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x04,wad,0x00,wad,guy,0x187,_|
		st := Caller(st);
		//|fp=0x0060|caller,0x00,0x04,wad,0x00,wad,guy,0x187,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x04,_,0x00,_,_,0x187,_|
		st := AndU160(st);
		//assert st.Peek(0) as u160 == st.evm.context.sender;
		stackLemma(st,st.Operands());
		st := block_0_0x059a(guy,wad,st);
		return st;
	}

	method block_0_0x059a(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x059a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [st'.evm.context.sender as u256,0x0,0x4,wad,0x0,wad,guy as u256,0x187,st'.Peek(8)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|caller,0x00,0x04,wad,0x00,wad,guy,0x187,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x04,wad,0x00,wad,guy,0x187,_|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x04,wad,0x00,wad,guy,0x187,_|
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x00,0x04,wad,0x00,wad,guy,0x187,_|
		st := MStore(st);
		//|fp=0x0060|0x00,0x04,wad,0x00,wad,guy,0x187,_| i.e. st.Read(0x00) == caller
		stackLemma(st,st.Operands());
		st := block_0_0x05b2(guy,wad,st);
		return st;
	}

	method block_0_0x05b2(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05b2
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x4,wad,0x0,wad,guy as u256,0x187,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x04,wad,0x00,wad,guy,0x187,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x04,wad,0x00,wad,guy,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|0x04,0x20,wad,0x00,wad,guy,0x187,_|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x04,0x20,wad,0x00,wad,guy,0x187,_|
		stackLemma(st,st.Operands());
		st := block_0_0x05b7(guy,wad,st);
		return st;
	}

	method block_0_0x05b7(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05b7
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x20,0x4,0x20,wad,0x0,wad,guy as u256,0x187,st'.Peek(8)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x04,0x20,wad,0x00,wad,guy,0x187,_|
		st := MStore(st);
		//|fp=0x0060|0x20,wad,0x00,wad,guy,0x187,_| i.e. st.Read(0x20) == 0x04
		stackLemma(st,st.Operands());
		st := block_0_0x05b8(guy,wad,st);
		return st;
	}
		
	method block_0_0x05b8(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05b8
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256 && st'.Read(0x20) == 0x04
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,guy as u256,0x187,st'.Peek(6)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,wad,0x00,wad,guy,0x187,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x00,wad,guy,0x187,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x00,wad,guy,0x187,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,wad,0x00,wad,guy,0x187,_|
		st := Keccak256(st);
		//|fp=0x0060|hash[caller,0x04],wad,0x00,wad,guy,0x187,_| 
		HashEquivalenceAxiom(st,st.Peek(0),st.evm.context.sender as u256,0x04);
		assert st.Peek(0) == Hash(st.evm.context.sender as u256,0x04);
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		st := Dup(st,6);
		//|fp=0x0060|guy,0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,guy,0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		stackLemma(st,st.Operands());
		st := block_0_0x05d6(guy,wad,st);
		return st;
	}

	method block_0_0x05d6(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05d6
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires st'.evm.stack.contents == [0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff,guy as u256,0x0,Hash(st'.evm.context.sender as u256,0x04),wad,0x00,wad,guy as u256,0x187,st'.Peek(9)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,guy,0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		st := AndU160(st);
		//|fp=0x0060|guy,0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,guy,0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		st := AndU160(st);
		//|fp=0x0060|guy,0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		st := Dup(st,2);
		//|fp=0x0060|0x00,guy,0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		st := MStore(st);
		//|fp=0x0060|0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_| i.e. st.Read(0x00) == guy
		stackLemma(st,st.Operands());
		st := block_0_0x05ef(guy,wad,st);
		return st;
	}

	method block_0_0x05ef(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05ef
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == guy as u256
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0x0,Hash(st'.evm.context.sender as u256,0x04),wad,0x00,wad,guy as u256,0x187,st'.Peek(7)]
	{
		var st := st';	
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,hash[caller,0x04],wad,0x00,wad,guy,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|hash[caller,0x04],0x20,wad,0x00,wad,guy,0x187,_|
		stackLemma(st,st.Operands());
		st := block_0_0x05f3(guy,wad,st);
		return st;
	}

	method block_0_0x05f3(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05f3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == guy as u256
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [Hash(st'.evm.context.sender as u256,0x04),0x20,wad,0x00,wad,guy as u256,0x187,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|hash[caller,0x04],0x20,wad,0x00,wad,guy,0x187,_|
		st := Dup(st,2);
		//|fp=0x0060|0x20,hash[caller,0x04],0x20,wad,0x00,wad,guy,0x187,_|
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_0_0x05f5(guy,wad,st);
		return st;
	}	

	method block_0_0x05f5(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05f5
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == guy as u256 && st'.Read(0x20) == Hash(st'.evm.context.sender as u256,0x04)
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [0x20,wad,0x00,wad,guy as u256,0x187,st'.Peek(6)]
	{
		var st := st';
		stackLemma(st,st.Operands());	
		//|fp=0x0060|0x20,wad,0x00,wad,guy,0x187,_|  i.e. st.Read(0x20) == hash[caller,0x04]
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x00,wad,guy,0x187,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x00,wad,guy,0x187,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,wad,0x00,wad,guy,0x187,_|
		st := Keccak256(st);
		//|fp=0x0060|hash[guy,hash[caller,0x04]],wad,0x00,wad,guy,0x187,_|
		HashEquivalenceAxiom(st,st.Peek(0),guy as u256,Hash(st'.evm.context.sender as u256,0x04));
		assert st.Peek(0) == Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04));	
		st := Dup(st,2);
		//|fp=0x0060|wad,hash[guy,hash[caller,0x04]],wad,0x00,wad,guy,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|hash[guy,hash[caller,0x04]],wad,wad,0x00,wad,guy,0x187,_|
		stackLemma(st,st.Operands());
		st := block_0_0x05fd(guy,wad,st);
		return st;
	}

	method block_0_0x05fd(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x05fd
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04)),wad,st'.Peek(2),st'.Peek(3),st'.Peek(4),st'.Peek(5),0x187,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|hash[guy,hash[caller,0x04]],wad,wad,0x00,wad,guy,0x187,_|
		st := SStore(st);
		//|fp=0x0060|wad,0x00,wad,guy,0x187,_| i.e. st.Load(hash[guy,hash[caller,0x04]]) == wad
		st := Pop(st);
		//|fp=0x0060|0x00,wad,guy,0x187,_|
		st := Dup(st,3);
		//|fp=0x0060|guy,0x00,wad,guy,0x187,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,guy,0x00,wad,guy,0x187,_|
		st := AndU160(st);
		//|fp=0x0060|guy,0x00,wad,guy,0x187,_|
		st := Caller(st);
		//|fp=0x0060|caller,guy,0x00,wad,guy,0x187,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,guy,0x00,wad,guy,0x187,_|
		st := AndU160(st);
		//|fp=0x0060|caller,guy,0x00,wad,guy,0x187,_|
		stackLemma(st,st.Operands());
		st := block_0_0x062d(guy,wad,st);
		return st;
	}

	method block_0_0x062d(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x062d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [st'.Peek(0),st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0x187,st'.Peek(6)]
	
	// Storage
	requires st'.Load(Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04))) == wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|caller,guy,0x00,wad,guy,0x187,_|
		st := PushN(st,32,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
		//|fp=0x0060|0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Dup(st,5);
		//|fp=0x0060|wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x60,0x60,wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,wad,0x60,0x60,wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := MStore(st); 
		//|fp=0x0060|0x60,0x60,wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		// i.e. st.Read(0x60) == wad
		stackLemma(st,st.Operands());
		st := block_0_0x0656(guy,wad,st);
		return st;
	}

	method block_0_0x0656(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0656
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),st'.Peek(5),st'.Peek(6),st'.Peek(7),st'.Peek(8),0x187,st'.Peek(10)]
	// Storage
	requires st'.Load(Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04))) == wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x60,wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,wad,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Swap(st,2);
		//|fp=0x0060|wad,0x60,0x80,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Pop(st);
		//|fp=0x0060|0x80,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0660(guy,wad,st);
		return st;
	}

	method block_0_0x0660(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0660
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [st'.Peek(0),0x60,0x80,st'.Peek(3),st'.Peek(4),st'.Peek(5),st'.Peek(6),st'.Peek(7),st'.Peek(8),0x187,st'.Peek(10)]
	// Storage
	requires st'.Load(Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04))) == wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x60,0x80,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925,caller,guy,0x00,wad,guy,0x187,_|
		st := LogN(st,3);
		//|fp=0x0060|0x00,wad,guy,0x187,_|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,0x00,wad,guy,0x187,_|
		st := Swap(st,1);
		//|fp=0x0060|0x00,0x01,wad,guy,0x187,_|
		st := Pop(st);
		//|fp=0x0060|0x01,wad,guy,0x187,_|
		st := Swap(st,3);
		//|fp=0x0060|0x187,wad,guy,0x01,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0669(guy,wad,st);
		return st;
	}

	method block_0_0x0669(guy: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0669
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires st'.evm.stack.contents == [0x187,st'.Peek(1),st'.Peek(2),0x1,st'.Peek(4)]
	// Storage
	requires st'.Load(Hash(guy as u256,Hash(st'.evm.context.sender as u256,0x04))) == wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x187,wad,guy,0x01,_|
		st := Swap(st,2);
		//|fp=0x0060|guy,wad,0x187,0x01,_|
		st := Pop(st);
		//|fp=0x0060|wad,0x187,0x01,_|
		st := Pop(st);
		//|fp=0x0060|0x187,0x01,_|
		assume {:axiom} st.IsJumpDest(0x187);
		st := Jump(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0187(guy,wad,st);
		return st;
	}

}
