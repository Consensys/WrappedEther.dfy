include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module util {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header
	import opened Int

	method block_0_0x00b7(bal: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00b7
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires 0 == st'.Operands()
	requires st'.evm.stack.contents == []
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		//|fp=0x0060|_|
		//|fp=0x0060||
		st := JumpDest(st);
		//|fp=0x0060|_|
		//|fp=0x0060||
		st := Stop(st);
		return st;
	}

	method block_1_0x00b7(bal: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00b7
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat
	requires callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		//|fp=0x0060|_|
		//|fp=0x0060||
		st := JumpDest(st);
		//|fp=0x0060|_|
		//|fp=0x0060||
		st := Stop(st);
		return st;
	}

	method block_0_0x0229(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0229
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		//|fp=0x0060|0x01,transferFrom|
		st := JumpDest(st);
		//|fp=0x0060|0x01,transferFrom|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x01,transferFrom|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x01,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x01,transferFrom|
		st := Dup(st,3);
		//|fp=0x0060|0x01,0x60,0x60,0x01,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|0x00,0x60,0x60,0x01,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|0x01,0x60,0x60,0x01,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|0x0,0x60,0x60,0x01,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|0x01,0x60,0x60,0x01,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x60,0x01,0x60,0x60,0x01,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,0x01,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0235(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0235(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0235
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires st'.evm.stack.contents == [0x60,0x60,st'.Peek(2),st'.Peek(3)]
	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x60,0x01,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,0x01,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		//|fp=0x0060|0x20,0x60,0x60,0x01,transferFrom|
		st := Add(st);
		//|fp=0x0060|0x80,0x60,0x01,transferFrom|
		st := Swap(st,2);
		//|fp=0x0060|0x01,0x60,0x80,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,transferFrom|
		st := Pop(st);
		stackLemma(st,st.Operands());
		st := block_0_0x023b(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x023b(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x023b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires st'.evm.stack.contents == [0x80,st'.Peek(1)]
	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x80,transferFrom|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,transferFrom|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,transferFrom|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,transferFrom|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,transferFrom|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,transferFrom|
		st := Return(st);
		return st;
	}
	
	method block_0_0x03d2(bal: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03d2
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	//requires 0 <= st'.Operands() <= 1
	requires st'.Operands() == 1
	//requires st'.Operands() == 0 ==> st'.evm.stack.contents == []
	requires st'.Operands() == 1 ==> st'.evm.stack.contents == [callSig] && callSig == 0xd0e30db0
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Stop(st);
		return st;
	}

	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	// from 00 -> af: |fp=0x0060|0x00b7| i.e. call data < 4 bytes
	method block_0_0x0440(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0440
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires 1 == st'.Operands()  
	requires st'.evm.stack.contents == [0xb7]
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xb7|
		st := JumpDest(st);
		//|fp=0x0060|0xb7|
		st := CallValue(st);
		//|fp=0x0060|callVal,0xb7|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,callVal,0xb7|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x03,callVal,0xb7|
		st := Caller(st);
		//|fp=0x0060|caller,0x00,0x03,callVal,0xb7|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,callVal,0xb7|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,callVal,0xb7,_|
		assert st.Peek(0) == st.evm.context.sender as u256;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,callVal,0xb7|
		st := AndU160(st);
		assert st.Peek(0) == st.evm.context.sender as u256;
		//|fp=0x0060|caller,0x00,0x03,callVal,0xb7|
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x00,0x03,callVal,0xb7|
		stackLemma(st,st.Operands());
		st := block_0_0x0474(st);
		return st;
	}

	method block_0_0x0474(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0474
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires 6 == st'.Operands() 
	requires st'.evm.stack.contents == [0x0,st'.evm.context.sender as u256,0x0,0x3,st'.evm.context.callValue,0xb7]
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x00,caller,0x00,0x03,callVal,0xb7|
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0475(st);
		return st;
	}
	
	method block_0_0x0475(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0475
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires 4 == st'.Operands() 
	requires st'.evm.stack.contents == [0x0,0x03,st'.evm.context.callValue,0xb7]
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x00,0x03,callVal,0xb7| 
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,callVal,0xb7|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,callVal,0xb7|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,callVal,0xb7|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,callVal,0xb7|
		stackLemma(st,st.Operands());
		st := block_0_0x047a(st);
		return st;
	}

	method block_0_0x047a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x047a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires 5 == st'.Operands() 
	requires st'.evm.stack.contents == [0x20,0x03,0x20,st'.evm.context.callValue,0xb7]
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);
		//|fp=0x0060|0x20,callVal,0xb7|
		stackLemma(st,st.Operands());
		st := block_0_0x047b(st);
		return st;
	}

	method block_0_0x047b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x047b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires 3 == st'.Operands() 
	// Static stack items
	requires st'.evm.stack.contents == [0x20,st'.evm.context.callValue,0xb7]
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,callVal,0xb7|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,callVal,0xb7|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,callVal,0xb7|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,callVal,0xb7|
		st := Keccak256(st);
		//|fp=0x0060|hash,callVal,0xb7|  i.e. hash == Keccak(...0x00,0x40)
		HashEquivalenceAxiom(st,st.Peek(0),st.evm.context.sender as u256,0x03);
		assert st.Peek(0) == Hash(st.evm.context.sender as u256,0x03);
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash,callVal,0xb7|
		st := Dup(st,3);
		//|fp=0x0060|callVal,0x00,hash,callVal,0xb7|
		st := Dup(st,3);
		//|fp=0x0060|hash,callVal,0x00,hash,callVal,0xb7|
		st := SLoad(st);
		//|fp=0x0060|bal,callVal,0x00,hash,callVal,0xb7|
		var bal := st.Peek(0);
		assert bal == st.Load(Hash(st.evm.context.sender as u256,0x03));
		stackLemma(st,st.Operands());
		st := block_0_0x0486(bal,st);
		return st;
	}

	method block_0_0x0486(bal: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0486
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires 6 == st'.Operands() 
	// Stack items
	requires st'.evm.stack.contents == [bal,st'.evm.context.callValue,st'.Peek(2),Hash(st'.evm.context.sender as u256,0x03),st'.Peek(4),0xb7]
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|bal,callVal,0x00,hash,callVal,0xb7|
		TotalSupplyBoundAxiom(st.Peek(0),st.Peek(1));
		assert (st.Peek(0) as nat + st.Peek(1) as nat) <= Int.MAX_U256 ; 
		st := Add(st);
		//|fp=0x0060|bal+callVal,0x00,hash,callVal,0xb7|
		//assert st.Peek(0) == bal + st.evm.context.callValue;
		st := Swap(st,3);
		//|fp=0x0060|callVal,0x00,hash,bal+callVal,0xb7|
		st := Pop(st);
		//|fp=0x0060|0x00,hash,bal+callVal,0xb7|
		st := Pop(st);
		//|fp=0x0060|hash,bal+callVal,0xb7|
		st := Dup(st,2);
		//|fp=0x0060|bal+callVal,hash,bal+callVal,0xb7|
		st := Swap(st,1);
		//|fp=0x0060|hash,bal+callVal,bal+callVal,0xb7|
		//assert st.Peek(0) == Hash(st.evm.context.sender as u256,0x03) && st.Peek(1) == bal + st.evm.context.callValue;
		st := SStore(st);
		//|fp=0x0060|bal+callVal,0xb7| i.e. st.Load(hash) == bal + callVal
		assert st.Load(Hash(st.evm.context.sender as u256,0x03)) == bal + st.evm.context.callValue;
		st := Pop(st);
		//|fp=0x0060|0xb7|
		stackLemma(st,st.Operands());
		st := block_0_0x048e(bal,st);
		return st;
	}

	method block_0_0x048e(bal: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x048e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires 1 == st'.Operands() 
	// Stack items
	requires st'.evm.stack.contents == [0xb7]
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xb7|
		st := Caller(st);
		//|fp=0x0060|caller,0xb7|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0xb7|
		st := AndU160(st);
		assert st.Peek(0) == st.evm.context.sender as u256;
		//|fp=0x0060|caller,0xb7|
		st := PushN(st,32,0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c);
		//|fp=0x0060|0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := CallValue(st);
		//|fp=0x0060|callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := MLoad(st);
		//|fp=0x0060|0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		stackLemma(st,st.Operands());
		st := block_0_0x04cb(bal,st);
		return st;
	}

	method block_0_0x04cb(bal: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04cb
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires 6 == st'.Operands() 
	// Stack items
	requires st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0xb7]
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat
	requires st'.evm.context.CallDataSize() < 0x04
	
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Dup(st,3);
		//|fp=0x0060|callVal,0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Dup(st,2);
		//|fp=0x0060|0x60,callVal,0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		stackLemma(st,st.Operands());
		st := block_0_0x04d0(bal,st);
		return st;
	}

	method block_0_0x04d0(bal: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04ce
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires 6 == st'.Operands() 
	// Stack items
	requires st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0xb7]
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Swap(st,2);
		//|fp=0x0060|callVal,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Pop(st);
		//|fp=0x0060|0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		stackLemma(st,st.Operands());
		st := block_0_0x04d4(bal,st);
		return st;
	}

	method block_0_0x04d4(bal: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04d4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires 4 == st'.Operands() 
	// Stack items
	requires st'.evm.stack.contents == [0x80,st'.Peek(1),st'.Peek(2),0xb7]
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat
	requires st'.evm.context.CallDataSize() < 0x04
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,0xb7|
		st := LogN(st,2);
		//|fp=0x0060|0xb7|
		assume {:axiom} st.IsJumpDest(0xb7);
		st := Jump(st);
		st := block_0_0x00b7(bal,st); 
		return st;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// from 3ca: //|fp=0x0060|0x3d2,callSig==0xd0e30db0| i.e from deposit, no other criteria
	// from a3 -> af: |fp=0x0060|0x00b7,callSig| i.e. call data >= 4 bytes but callSig doesn't match the defined functions
	method block_1_0x0440(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0440
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() ==2 
	requires st'.evm.stack.contents == [0x3d2,callSig] || st'.evm.stack.contents == [0x0b7,callSig]
	
	requires st'.Peek(0) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(0) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|(0xb7||0x3d2),callSig|
		st := JumpDest(st);
		//|fp=0x0060|(0xb7||0x3d2),callSig|
		st := CallValue(st);
		//|fp=0x0060|callVal,(0xb7||0x3d2),callSig|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,callVal,(0xb7||0x3d2),callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x03,callVal,(0xb7||0x3d2),callSig|
		st := Caller(st);
		//|fp=0x0060|caller,0x00,0x03,callVal,(0xb7||0x3d2),callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,callVal,(0xb7||0x3d2),callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,callVal,0xb7,_|
		assert st.Peek(0) == st.evm.context.sender as u256;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,callVal,(0xb7||0x3d2),callSig|
		stackLemma(st,st.Operands());
		st := block_1_0x0472(callSig,st);
		return st;
	}

	method block_1_0x0472(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0472
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7 
	requires st'.evm.stack.contents == [0xffffffffffffffffffffffffffffffffffffffff,st'.evm.context.sender as u256,0x0,0x03,st'.evm.context.callValue,0x3d2,callSig]
								|| st'.evm.stack.contents == [0xffffffffffffffffffffffffffffffffffffffff,st'.evm.context.sender as u256,0x0,0x03,st'.evm.context.callValue,0x0b7,callSig]
	
	requires st'.Peek(5) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(5) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,callVal,(0xb7||0x3d2),callSig|
		st := AndU160(st);
		assert st.Peek(0) == st.evm.context.sender as u256;
		//|fp=0x0060|caller,0x00,0x03,callVal,(0xb7||0x3d2),callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x00,0x03,callVal,(0xb7||0x3d2),callSig|
		stackLemma(st,st.Operands());
		st := block_1_0x0474(callSig,st);
		return st;
	}

	method block_1_0x0474(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)	
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0474
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7 
	requires st'.evm.stack.contents == [0x0,st'.evm.context.sender as u256,0x0,0x03,st'.evm.context.callValue,0x3d2,callSig]
								|| st'.evm.stack.contents == [0x0,st'.evm.context.sender as u256,0x0,0x03,st'.evm.context.callValue,0x0b7,callSig]
	
	requires st'.Peek(5) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(5) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_1_0x0475(callSig,st);
		return st;
	}
	
	method block_1_0x0475(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0475
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 5 
	requires st'.evm.stack.contents == [0x0,0x03,st'.evm.context.callValue,0x3d2,callSig] 
								|| st'.evm.stack.contents == [0x0,0x03,st'.evm.context.callValue,0x0b7,callSig] 
	
	requires st'.Peek(3) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(3) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x00,0x03,callVal,(0xb7||0x3d2),callSig| i.e. st.Read(0x00) == caller
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,callVal,(0xb7||0x3d2),callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,callVal,(0xb7||0x3d2),callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,callVal,(0xb7||0x3d2),callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,callVal,(0xb7||0x3d2),callSig|
		stackLemma(st,st.Operands());
		st := block_1_0x047a(callSig,st);
		return st;
	}

	method block_1_0x047a(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x047a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 6 
	requires st'.evm.stack.contents == [0x20,0x03,0x20,st'.evm.context.callValue,0x3d2,callSig]
						|| st'.evm.stack.contents == [0x20,0x03,0x20,st'.evm.context.callValue,0x0b7,callSig]
	
	requires st'.Peek(4) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(4) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';	
		stackLemma(st,st.Operands());
		st := MStore(st);
		//|fp=0x0060|0x20,callVal,(0xb7||0x3d2),callSig|
		stackLemma(st,st.Operands());
		assert st.Read(0x20) == 0x03;
		st := block_1_0x047b(callSig,st);
		return st;
	}

	method block_1_0x047b(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x047b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires st'.evm.stack.contents == [0x20,st'.evm.context.callValue,0x3d2,callSig]
								|| st'.evm.stack.contents == [0x20,st'.evm.context.callValue,0x0b7,callSig]
	
	requires st'.Peek(2) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(2) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,callVal,(0xb7||0x3d2),callSig|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,callVal,(0xb7||0x3d2),callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,callVal,(0xb7||0x3d2),callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,callVal,(0xb7||0x3d2),callSig|
		st := Keccak256(st);
		//|fp=0x0060|hash,callVal,(0xb7||0x3d2),callSig|  i.e. hash == Keccak(...0x00,0x40)
		HashEquivalenceAxiom(st,st.Peek(0),st.evm.context.sender as u256,0x03);
		assert st.Peek(0) == Hash(st.evm.context.sender as u256,0x03);
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash,callVal,(0xb7||0x3d2),callSig|
		st := Dup(st,3);
		//|fp=0x0060|callVal,0x00,hash,callVal,(0xb7||0x3d2),callSig|
		st := Dup(st,3);
		//|fp=0x0060|hash,callVal,0x00,hash,callVal,(0xb7||0x3d2),callSig|
		st := SLoad(st);
		//|fp=0x0060|bal,callVal,0x00,hash,callVal,(0xb7||0x3d2),callSig|
		var bal := st.Peek(0);
		assert bal == st.Load(Hash(st.evm.context.sender as u256,0x03));
		stackLemma(st,st.Operands());
		st := block_1_0x0486(bal,callSig,st);
		return st;
	}

	method block_1_0x0486(bal: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0486
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Stack items
	requires st'.evm.stack.contents == [bal,st'.evm.context.callValue,st'.Peek(2),Hash(st'.evm.context.sender as u256,0x03),st'.Peek(4),0x3d2,callSig]
								|| st'.evm.stack.contents == [bal,st'.evm.context.callValue,st'.Peek(2),Hash(st'.evm.context.sender as u256,0x03),st'.Peek(4),0x0b7,callSig] 
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal

	requires st'.Peek(5) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(5) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|bal,callVal,0x00,hash,callVal,(0xb7||0x3d2),callSig|
		TotalSupplyBoundAxiom(st.Peek(0),st.Peek(1));
		assert (st.Peek(0) as nat + st.Peek(1) as nat) <= Int.MAX_U256 ; 
		st := Add(st);
		//|fp=0x0060|bal+callVal,0x00,hash,callVal,(0xb7||0x3d2),callSig|
		assert st.Peek(0) == bal + st.evm.context.callValue;
		st := Swap(st,3);
		//|fp=0x0060|callVal,0x00,hash,bal+callVal,(0xb7||0x3d2),callSig|
		st := Pop(st);
		//|fp=0x0060|0x00,hash,bal+callVal,(0xb7||0x3d2),callSig|
		st := Pop(st);
		//|fp=0x0060|hash,bal+callVal,(0xb7||0x3d2),callSig|
		st := Dup(st,2);
		//|fp=0x0060|bal+callVal,hash,bal+callVal,(0xb7||0x3d2),callSig|
		st := Swap(st,1);
		//|fp=0x0060|hash,bal+callVal,bal+callVal,(0xb7||0x3d2),callSig|
		assert st.Peek(0) == Hash(st.evm.context.sender as u256,0x03) && st.Peek(1) == bal + st.evm.context.callValue;
		st := SStore(st);
		//|fp=0x0060|bal+callVal,(0xb7||0x3d2),callSig| i.e. st.Load(hash) == bal + callVal
		assert st.Load(Hash(st.evm.context.sender as u256,0x03)) == bal + st.evm.context.callValue;
		st := Pop(st);
		//|fp=0x0060|(0xb7||0x3d2),callSig|
		stackLemma(st,st.Operands());
		st := block_1_0x048e(bal,callSig,st);
		return st;
	}

	method block_1_0x048e(bal: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x048e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Stack items
	requires st'.evm.stack.contents == [0x3d2,callSig] || st'.evm.stack.contents == [0x0b7,callSig] 
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat

	requires st'.Peek(0) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(0) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|(0xb7||0x3d2),callSig|
		st := Caller(st);
		//|fp=0x0060|caller,(0xb7||0x3d2),callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,(0xb7||0x3d2),callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,(0xb7||0x3d2),callSig|
		assert st.Peek(0) == st.evm.context.sender as u256;
		st := PushN(st,32,0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c);
		//|fp=0x0060|0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := CallValue(st);
		//|fp=0x0060|callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := MLoad(st);
		//|fp=0x0060|0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		stackLemma(st,st.Operands());
		st := block_1_0x04cb(bal,callSig,st);
		return st;
	}

	method block_1_0x04cb(bal: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04cb
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Stack items
	requires st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0x3d2,callSig] 
								|| st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0x0b7,callSig] 
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat

	requires st'.Peek(5) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(5) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Dup(st,3);
		//|fp=0x0060|callVal,,0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x60,callVal,,0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		stackLemma(st,st.Operands());
		st := block_1_0x04cf(bal,callSig,st);
		return st;
	}

	method block_1_0x04cf(bal: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04ce
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Stack items
	requires st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0x3d2,callSig]
								|| st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0x0b7,callSig] 
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat

	requires st'.Peek(5) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(5) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,callVal,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Swap(st,2);
		//|fp=0x0060|callVal,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Pop(st);
		//|fp=0x0060|0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		stackLemma(st,st.Operands());
		st := block_1_0x04d4(bal,callSig,st);
		return st;
	}

	method block_1_0x04d4(bal: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x04d4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Stack items
	requires st'.evm.stack.contents == [0x80,st'.Peek(1),st'.Peek(2),0x3d2,callSig]
								|| st'.evm.stack.contents == [0x80,st'.Peek(1),st'.Peek(2),0x0b7,callSig] 
	// Storage
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) as nat == bal as nat +  st'.evm.context.callValue as nat

	requires st'.Peek(3) == 0x3d2 ==> callSig == 0xd0e30db0
	requires st'.Peek(3) == 0x0b7 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0xe1fffcc4923d04b559f4d29a8bfc6cda4eb5b0d3c460751c2402c5c5cc9109c,caller,(0xb7||0x3d2),callSig|
		st := LogN(st,2);
		//|fp=0x0060|(0xb7||0x3d2),callSig|
		assume {:axiom} st.IsJumpDest(0xb7);
		assume {:axiom} st.IsJumpDest(0x3d2);
		st := Jump(st);
		stackLemma(st,st.Operands());
		match st.PC() {
			case 0xb7 => { st := block_1_0x00b7(bal,callSig,st); }
			case 0x3d2 => { st := block_0_0x03d2(bal,callSig,st); }
	}
		return st;
	}

	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	// from (transferFrom) 223: 	|fp=0x0060|wad,dst*,src*,0x229,transferFrom| 					& call value == 0 

	method block_0_0x068c(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x068c
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() ==5
	// Dynamic stack items
	requires st'.evm.stack.contents == [wad,dst as u256,src as u256,0x229,st'.Peek(4)] 
	requires callSig == 0x23b872dd
	
	requires st'.evm.context.callValue == 0
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,dst*,src*,0x229,transferFrom|
		st := JumpDest(st);
		//|fp=0x0060|wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,7);
		//|fp=0x0060|src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == src as u256;
		stackLemma(st,st.Operands());
		st := block_0_0x06ab(src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x06ab(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06ab
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	// Stack items
	requires st'.evm.stack.contents == [src as u256,0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == src as u256;
		st := Dup(st,2);
		//|fp=0x0060|0x00,src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|						
		stackLemma(st,st.Operands());
		st := block_0_0x06c3(src,dst,wad,callSig,st);
		return st;
	}
		
	method block_0_0x06c3(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06c3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() == 9
	// Stack items
	requires st'.evm.stack.contents == [0,0x03,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|	
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x06c8(src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x06c8(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06c8
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() == 10
	// Stack items
	requires st'.evm.stack.contents == [0x20,0x03,0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x03,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_0_0x06c9(src,dst,wad,callSig,st);
		return st;
	}
	
	method block_0_0x06c9(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06c9
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 8
	// Stack items
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Keccak256(st);
		//|fp=0x0060|hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		HashEquivalenceAxiom(st,st.Peek(0),src as u256,0x03);
		assert st.Peek(0) == Hash(src as u256,0x03);
		assert st.evm.stack.contents == [Hash(src as u256,0x03),wad,0x0,wad,dst as u256,src as u256,0x229,st.Peek(7)]; 
		st := SLoad(st);
		//|fp=0x0060|bal,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		var bal := st.Peek(0);
		assert bal == st.Load(Hash(src as u256,0x03));
		st := Lt(st);
		//|fp=0x0060|bal < wad,0x0,wad,dst*,src*,0x229,transferFrom|
		//assert st.Peek(0) == (if bal < wad then 1 else 0);
		st := IsZero(st);
		//|fp=0x0060|bal < wad,0x0,wad,dst*,src*,0x229,transferFrom|
		//assert (st.Peek(0) == (if bal < wad then 0 else 1) );
		stackLemma(st,st.Operands());
		st := block_0_0x06d2(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x06d2(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06d2
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Stack items
	requires st'.Peek(0) == if bal < wad then 0 else 1	
	requires st'.evm.stack.contents == [st'.Peek(0),0x0,wad,dst as u256,src as u256,0x229,st'.Peek(6)] 

	// Storage
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|{1,0},0x0,wad,dst*,src*,0x229,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|{0,1},0x0,wad,dst*,src*,0x229,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|{1,0},0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push2(st,0x06dc);
		//|fp=0x0060|0x06dc,{1,0},0x0,wad,dst*,src*,0x229,transferFrom|
		assume {:axiom} st.IsJumpDest(0x6dc);
		st := JumpI(st);
		if st.PC() == 0x6dc { 
			// i.e. bal >= wad
			//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
			stackLemma(st,st.Operands());
			st := block_0_0x06dc(bal,src,dst,wad,callSig,st); 
			return st;
		} 
 		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x0,0x0,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Revert(st); // i.e. balOfCaller (or balOfSrc) < wad
		return st;
	}

	method block_0_0x06dc(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06dc
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Stack items
	requires st'.evm.stack.contents == [0x0,wad,dst as u256,src as u256,0x229,st'.Peek(5)] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := JumpDest(st);
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := Caller(st);
		//|fp=0x0060|caller,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|caller*,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());		// NB: sometimes as extra stack lemma can help!
		assert st.Peek(0) == st.evm.context.sender as u256;
		st := Dup(st,5);
		//|fp=0x0060|src*,caller*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,caller*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src*,caller*,0x0,wad,dst*,src*,0x229,transferFrom|
		//assert st.Peek(0) == src as u256;
		st := Eq(st);
		//|fp=0x0060|src* == caller*,0x0,wad,dst*,src*,0x229,transferFrom|
		//assert st.Peek(0) == if src == st.evm.context.sender then 1 else 0;
		stackLemma(st,st.Operands());
		st := block_0_0x070c(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x070c(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x070c
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Stack items
	requires st'.Peek(0) == if src == st'.evm.context.sender then 1 else 0
	requires st'.evm.stack.contents == [st'.Peek(0),0x0,wad,dst as u256,src as u256,0x229,st'.Peek(6)] 
				
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|src == caller,0x0,wad,dst*,src*,0x229,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|src != caller,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|src != caller,src != caller,0x0,wad,dst*,src*,0x229,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|src == caller,src != caller,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push2(st,0x07b4);
		//|fp=0x0060|0x7b4,src == caller,src != caller,0x0,wad,dst*,src*,0x229,transferFrom|
		assume {:axiom} st.IsJumpDest(0x7b4);
		st := JumpI(st);
		if st.PC() == 0x7b4 { 
			// src == caller
			stackLemma(st,st.Operands());
			st := block_0_0x07b4(bal,src,dst,wad,callSig,st); 
			return st;
		}
		//|fp=0x0060|0x1,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0737(bal,src,dst,wad,callSig,st);
		return st;
	}

	// src != caller
	method block_0_0x0737(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0737
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Stack items
	requires st'.evm.stack.contents == [0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 
	
	requires src != st'.evm.context.sender
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,7);
		//|fp=0x0060|src*,0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src*,0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == src as u256;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src*,0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == src as u256;
		st := Dup(st,2);
		//|fp=0x0060|0x0,src*,0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st); 
		//|fp=0x0060|0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| i.e.st.Read(0x0) == src*
		stackLemma(st,st.Operands());
		assert st.Read(0x0) == src as u256;
		st := block_0_0x0768(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0768(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0768
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() == 9
	// Stack items
	requires st'.evm.stack.contents == [0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 
	
	requires src != st'.evm.context.sender
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x0,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		st := Swap(st,1);
		//|fp=0x0060|0x04,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x04,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		stackLemma(st,st.Operands());
		st := block_0_0x076d(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x076d(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x076d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 
	// Stack height(s)
	requires st'.Operands() == 10
	// Stack items
	requires st'.evm.stack.contents == [0x20,0x04,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 
	
	requires src != st'.evm.context.sender
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';	
		stackLemma(st,st.Operands());
		st := MStore(st); // i.e. st.Read(0x20) == 0x04
		//|fp=0x0060|0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		stackLemma(st,st.Operands());
		st := block_0_0x076e(bal,src,dst,wad,callSig,st);
		return st;
	}
		
	method block_0_0x076e(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x076e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 && st'.Read(0x20) == 0x04
	// Stack height(s)
	requires st'.Operands() == 8
	// Stack items
	requires st'.evm.stack.contents == [0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 
	
	requires src != st'.evm.context.sender
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';	
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		stackLemma(st,st.Operands());
		st := block_0_0x0773(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0773(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0773
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 && st'.Read(0x20) == 0x04
	// Stack height(s)
	requires st'.Operands() == 9
	// Stack items
	requires st'.evm.stack.contents == [0x0,0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 
	
	requires src != st'.evm.context.sender
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom| 
		st := Keccak256(st);
		//|fp=0x0060|hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		HashEquivalenceAxiom(st,st.Peek(0),src as u256,0x04);
		assert st.Peek(0) == Hash(src as u256,0x04);
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Caller(st);
		//|fp=0x0060|caller,0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		assert st.Peek(0) == st.evm.context.sender as u256;
		//|fp=0x0060|caller*,0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller*,0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		assert st.Peek(0) == st.evm.context.sender as u256;
		//|fp=0x0060|caller*,0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x0,caller*,0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x07a4(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x07a4(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07a4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	// Stack items
	requires st'.evm.stack.contents == [0x0,st'.evm.context.sender as u256,0x0,Hash(src as u256,0x04),0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 
	
	requires src != st'.evm.context.sender
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,caller*,0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x07a5(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x07a5(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07a5
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 9
	// Stack items
	requires st'.evm.stack.contents == [0x0,Hash(src as u256,0x04),0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 
	
	requires src != st'.evm.context.sender
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x0,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|hash,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x20,hash,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := block_0_0x07aa(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x07aa(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07aa
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == st'.evm.context.sender as u256 
	// Stack height(s)
	requires st'.Operands() == 10
	// Stack items
	requires st'.evm.stack.contents == [0x20,Hash(src as u256,0x04),0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 
	
	requires src != st'.evm.context.sender
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());	
		//|fp=0x0060|0x20,hash,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st); // st.Read(0x20) == hash(0x00,0x40)
		//|fp=0x0060|0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		//assert st.Read(0x20) == Hash(src as u256,0x04);
		st := block_0_0x07ab(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x07ab(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07ab
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == st'.evm.context.sender as u256 && st'.Read(0x20) == Hash(src as u256,0x04)
	// Stack height(s)
	requires st'.Operands() == 8
	// Stack items
	requires st'.evm.stack.contents == [0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 
	
	requires src != st'.evm.context.sender
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x40,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Keccak256(st);
		//|fp=0x0060|hash,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		HashEquivalenceAxiom(st,st.Peek(0),st.evm.context.sender as u256,Hash(src as u256,0x04));
		assert st.Peek(0) == Hash(st.evm.context.sender as u256,Hash(src as u256,0x04));
		st := SLoad(st);
		//|fp=0x0060|Load(hash),0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		var allowance := st.Peek(0);
		assert allowance == st.Load(Hash(st.evm.context.sender as u256,Hash(src as u256,0x04)));
		st := Eq(st); // i.e. solidity .... allowance[src][msg.sender] != uint(-1)
		//|fp=0x0060|allowance == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		//assert st.Peek(0) == if allowance == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff then 1 else 0;
		st := IsZero(st);
		//|fp=0x0060|allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,src*,0x229,transferFrom|
		//assert st.Peek(0) == if allowance == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff then 0 else 1;
		//assert st.evm.stack.contents == [st.Peek(0),0x0,wad,dst as u256,src as u256,0x229,st.Peek(6)] ;
		stackLemma(st,st.Operands());
		st := block_0_0x07b4(bal,src,dst,wad,callSig,st);
		return st;
	}

	
	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	//from 7ae: |fp=0x0060|{0,1},0x0,wad,dst*,src*,0x229,transferFrom|
	//from 70c: |fp=0x0060|0x0,0x0,wad,dst*,src*,0x229,transferFrom|
	
	method block_0_0x07b4(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07b4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() ==7
	// Stack items
	requires st'.evm.stack.contents == [st'.Peek(0),0x0,wad,dst as u256,src as u256,0x229,st'.Peek(6)] 
	
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			var flag := if allowance == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff then 0 else 1;
			(src != st'.evm.context.sender && st'.Peek(0) == flag) || (src == st'.evm.context.sender && st'.Peek(0) == 0x0)
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
		var flag := if allowance == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff then 0 else 1;
		var flag' := if flag == 0 then 1 else 0;
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|{0,1},0x0,wad,dst*,src*,0x229,transferFrom|
		st := JumpDest(st);
		//|fp=0x0060|{0,1},0x0,wad,dst*,src*,0x229,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|{1,0},0x0,wad,dst*,src*,0x229,transferFrom|
		assert src != st.evm.context.sender ==> st.Peek(0) == flag'; 
		assert src == st.evm.context.sender ==> st.Peek(0) == 0x01;
		st := Push2(st,0x08cf);
		//|fp=0x0060|0x8cf,{1,0},0x0,wad,dst*,src*,0x229,transferFrom|
		assume {:axiom} st.IsJumpDest(0x8cf);
		st := JumpI(st);
		if st.PC() == 0x8cf { 
			// allowance[src][msg.sender] == uint(-1)
			//assert src == st.evm.context.sender || (src != st.evm.context.sender && allowance == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
			stackLemma(st,st.Operands());
			st := block_0_0x08cf(bal,src,dst,wad,callSig,st); 
			return st;
		} 
		//assert src != st.evm.context.sender && allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,7);
		//|fp=0x0060|src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x07c0(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x07c0(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07c0
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires st'.evm.stack.contents == [src as u256,0x0,0x04,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 
	
	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == src as u256;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		assert st.Peek(0) == src as u256;
		//|fp=0x0060|src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x0,src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x07ee(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x07ee(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07ee
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x04,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 
	
	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x07f1(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x07f1(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07f1
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x20,0x04,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 
	
	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x04,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x04,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x07f4(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x07f4(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07f4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 && st'.Read(0x20) == 0x04
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 
	
	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) == 0x0 && st.Peek(1) == 0x40);
		st := Keccak256(st);
		//|fp=0x0060|hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		HashEquivalenceAxiom(st,st.Peek(0),src as u256,0x04);
		assert st.Peek(0) == Hash(src as u256,0x04);
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x07fc(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x07fc(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07fc
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x0,Hash(src as u256,0x04),wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Caller(st);
		//|fp=0x0060|caller,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|caller*,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == st.evm.context.sender as u256;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|caller*,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == st.evm.context.sender as u256;
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller*,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x082a(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x082a(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x082a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x0,st'.evm.context.sender as u256,0x0,Hash(src as u256,0x04),wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);
		//|fp=0x0060|0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x082b(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x082b(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x082b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == st'.evm.context.sender as u256 
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x0,Hash(src as u256,0x04),wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|hash,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x20,hash,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0830(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0830(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0830
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 10
	requires st'.evm.stack.contents == [0x20,Hash(src as u256,0x04),0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0831(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0831(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0831
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == st'.evm.context.sender as u256 && st'.Read(0x20) == Hash(src as u256,0x04)
	// Stack height(s)
	requires st'.Operands() == 8
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Keccak256(st);
		//|fp=0x0060|hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		HashEquivalenceAxiom(st,st.Peek(0),st.evm.context.sender as u256,Hash(src as u256,0x04));
		assert st.Peek(0) == Hash(st.evm.context.sender as u256,Hash(src as u256,0x04));
		stackLemma(st,st.Operands());
		st := block_0_0x0837(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0837(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0837
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x0) == st'.evm.context.sender as u256 && st'.Read(0x20) == Hash(src as u256,0x04))
	// Stack height(s)
	requires st'.Operands() == 8
	requires st'.evm.stack.contents == [Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)),wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := SLoad(st);
		//|fp=0x0060|Load(hash),wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Lt(st);
		//|fp=0x0060|Load(hash)<wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|{0,1},0x0,wad,dst*,src*,0x229,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|{1,0},0x0,wad,dst*,src*,0x229,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|{0,1},0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push2(st,0x0844);
		//|fp=0x0060|0x844,{0,1},0x0,wad,dst*,src*,0x229,transferFrom|
		assume {:axiom} st.IsJumpDest(0x844);
		st := JumpI(st);
		if st.PC() == 0x844 { 
			// i.e. Load(hash) >=  wad
			//assert (st.Peek(0) == 0x0 && st.Peek(1) == wad && st.Peek(2) == dst as u256 && st.Peek(3) == src as u256);
			stackLemma(st,st.Operands());
			st := block_0_0x0844(bal,src,dst,wad,callSig,st); 
			return st;
		} 
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0842(src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0842(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0842
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance < wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x0,0x0,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Revert(st);
		return st;
	}

	method block_0_0x0844(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0844
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	requires st'.evm.stack.contents == [0x0,wad,dst as u256,src as u256,0x229,st'.Peek(5)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := JumpDest(st);
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,7);
		//|fp=0x0060|src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == src as u256;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0876(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0876(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0876
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 
	// Stack height(s)
	requires st'.Operands() ==11
	// Static stack items
	requires st'.evm.stack.contents == [0xffffffffffffffffffffffffffffffffffffffff,src as u256,0x0,0x04,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == src as u256;
		st := Dup(st,2);
		//|fp=0x0060|0x00,src*,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0879(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0879(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0879
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() ==9
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x04,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x0,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x04,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x04,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x04,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x087e(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x087e(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x087e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() ==10
	// Static stack items
	requires st'.evm.stack.contents == [0x20,0x04,0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());	
		st := MStore(st);
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x087f(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x087f(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x087f
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 && st'.Read(0x20) == 0x04
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Keccak256(st);
		//|fp=0x0060|hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		HashEquivalenceAxiom(st,st.Peek(0),src as u256,0x04);
		assert st.Peek(0) == Hash(src as u256,0x04);
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Caller(st);
		//|fp=0x0060|caller,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|caller*,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == st.evm.context.sender as u256;
		assert st.evm.stack.contents == [st.evm.context.sender as u256,0x0,Hash(src as u256,0x04),wad,0x0,wad,dst as u256,src as u256,0x229,st.Peek(9)]; 
		
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|caller*,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == st.evm.context.sender as u256 ;
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller*,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents == [0x0,st.evm.context.sender as u256,0x0,Hash(src as u256,0x04),wad,0x0,wad,dst as u256,src as u256,0x229,st.Peek(10)]; 
		st := block_0_0x08b5(bal,src,dst,wad,callSig,st);
		return st;
	}
	
	method block_0_0x08b5(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08b5
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x0,st'.evm.context.sender as u256,0x0,Hash(src as u256,0x04),wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,caller*,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x08b6(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x08b6(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08b6
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60  && st'.Read(0x0) == st'.evm.context.sender as u256 
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x0,Hash(src as u256,0x04),wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|hash,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x20,hash,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x08bb(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x08bb(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08bb
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == st'.evm.context.sender as u256 
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires st'.evm.stack.contents == [0x20,Hash(src as u256,0x04),0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 
	
	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,hash,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x08bc(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x08bc(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08bc
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == st'.evm.context.sender as u256 && st'.Read(0x20) == Hash(src as u256,0x04)
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 
	
	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Keccak256(st);
		HashEquivalenceAxiom(st,st.Peek(0),st'.evm.context.sender as u256,Hash(src as u256,0x04));
		assert st.Peek(0) == Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04));
		//|fp=0x0060|hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,3);
		//|fp=0x0060|hash,wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x08c6(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x08c6(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08c6
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	requires st'.evm.stack.contents == [Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)),wad,0x0,Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)),wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 
	
	requires st'.Operands() == 15 ==> ((st'.Peek(9) == 0xbdb && st'.Peek(13) == 0x3b0))
	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires var allowance := st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04)));
			allowance != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
			&& allowance >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|hash,wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := SLoad(st);
		//|fp=0x0060|Load(hash),wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		var allowance := st.Peek(0);
		assert allowance == st.Load(Hash(st.evm.context.sender as u256,Hash(src as u256,0x04)));
		assert st.Peek(1) <= st.Peek(0); // true because of block 0x837
		st := Sub(st);
		//|fp=0x0060|Load(hash)-wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,3);
		//|fp=0x0060|wad,0x0,hash,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x0,hash,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|hash,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|Load(hash)-wad,hash,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == allowance - wad;
		st := Swap(st,1);
		//|fp=0x0060|hash,Load(hash)-wad,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		//assert st.Peek(0) == Hash(st.evm.context.sender as u256,Hash(src as u256,0x04)) && st.Peek(1) == allowance - wad;
		st := SStore(st); // i.e. update balance (or allowance??)
		//|fp=0x0060|Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		NoCollisionsAxiom(Hash(st.evm.context.sender as u256,Hash(src as u256,0x04)),Hash(src as u256,0x03));
		stackLemma(st,st.Operands());
		st := block_0_0x08ce(allowance,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x08ce(allowance: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08ce
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	requires allowance >= wad
	requires st'.evm.stack.contents == [allowance-wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(6)] 

	requires src != st'.evm.context.sender // and allowance exists
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	requires st'.Load(Hash(st'.evm.context.sender as u256,Hash(src as u256,0x04))) == allowance - wad
	//  i.e this won't be tracked going forward, mostly due to block 8cf also being for when src == caller
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x08cf(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x08cf(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08cf
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	requires st'.evm.stack.contents == [0x0,wad,dst as u256,src as u256,0x229,st'.Peek(5)] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := JumpDest(st);
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,7);
		//|fp=0x0060|src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == src as u256;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0901(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0901(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0901
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0xffffffffffffffffffffffffffffffffffffffff,src as u256,0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		assert st.Peek(0) == src as u256;
		//|fp=0x0060|src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x00,src*,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0904(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0904(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0904
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x0,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0909(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0909(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0909
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires st'.evm.stack.contents == [0x20,0x03,0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x090a(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x090a(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x090a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		assert st.Peek(0) == 0x40;
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Keccak256(st);
		//|fp=0x0060|hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		HashEquivalenceAxiom(st,st.Peek(0),src as u256,0x03);
		assert st.Peek(0) == Hash(src as u256,0x03);
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,3);
		//|fp=0x0060|hash,wad,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := SLoad(st);
		//|fp=0x0060|Load(hash),wad,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0915(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0915(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0915
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	requires st'.evm.stack.contents == [bal,wad,0x0,Hash(src as u256,0x03),wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 

	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|Load(hash),wad,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|Load(hash)-wad,0x00,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,3);
		//|fp=0x0060|wad,0x00,hash,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x00,hash,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|hash,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|Load(hash)-wad,hash,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|hash,Load(hash)-wad,Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := SStore(st);
		//|fp=0x0060|Load(hash)-wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Load(Hash(src as u256,0x03)) == bal - wad;
		st := Pop(st);
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x091d(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x091d(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x091d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	requires st'.evm.stack.contents == [0x0,wad,dst as u256,src as u256,0x229,st'.Peek(5)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,6);
		//|fp=0x0060|dst*,0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,dst*,0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|dst*,0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == dst as u256 ;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,dst*,0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|dst*,0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(0) == dst as u256;
		st := Dup(st,2);
		//|fp=0x0060|0x0,dst*,0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0950(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0950(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0950
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x0,dst as u256,0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		
		st := MStore(st);
		//|fp=0x0060|0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0951(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0951(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0951
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == dst as u256
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(8)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0956(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0956(bal: u256,src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0956
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == dst as u256 
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires st'.evm.stack.contents == [0x20,0x03,0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x0957(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0957(bal: u256,src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0957
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == dst as u256 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(7)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x40,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Keccak256(st);
		//|fp=0x0060|hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		HashEquivalenceAxiom(st,st.Peek(0),dst as u256,0x03);
		assert st.Peek(0) == Hash(dst as u256,0x03);
		assert st.evm.stack.contents == [Hash(dst as u256,0x03),wad,0x0,wad,dst as u256,src as u256,0x229,st.Peek(7)] ;
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		
		st := Dup(st,3);
		//|fp=0x0060|wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,3);
		//|fp=0x0060|hash,wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := SLoad(st);
		//|fp=0x0060|Load(hash),wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		var dBal := st.Peek(0);
		assert dBal == st.Load(Hash(dst as u256,0x03));

		TotalSupplyBoundAxiom(st.Peek(0),st.Peek(1));
		assert (st.Peek(0) as nat + st.Peek(1) as nat) <= (Int.MAX_U256 ); 
		st := Add(st);
		//|fp=0x0060|Load(hash)+wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents == [st.Peek(0),0x0,Hash(dst as u256,0x03),wad,0x0,wad,dst as u256,src as u256,0x229,st.Peek(9)] ;
		st := block_0_0x0963(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0963(dBal: u256, bal: u256,src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0963
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) == dBal

	requires st'.Peek(0) as nat == dBal as nat + wad as nat <= Int.MAX_U256 
	requires st'.evm.stack.contents == [st'.Peek(0),0x0,Hash(dst as u256,0x03),wad,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(9)] 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|Load(hash)+wad,0x0,hash,wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,3);
		//|fp=0x0060|wad,0x0,hash,Load(hash)+wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x0,hash,Load(hash)+wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|hash,Load(hash)+wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|Load(hash)+wad,hash,Load(hash)+wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|hash,Load(hash)+wad,Load(hash)+wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := SStore(st);
		//|fp=0x0060|Load(hash)+wad,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,3);
		//|fp=0x0060|dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		NoCollisionsAxiom(Hash(dst as u256,0x03),Hash(src as u256,0x03));
		stackLemma(st,st.Operands());
		st := block_0_0x096b(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x096b(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x096b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	requires st'.evm.stack.contents == [dst as u256,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(6)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		assert st.Peek(0) == dst as u256 ;
		//|fp=0x0060|dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,5);
		//|fp=0x0060|src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := AndU160(st);
		stackLemma(st,st.Operands());
		assert st.Peek(0) == src as u256 ;
		//|fp=0x0060|src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := PushN(st,32,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
		//|fp=0x0060|0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,5);
		//|fp=0x0060|wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x09bc(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x09bc(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09bc
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	requires st'.evm.stack.contents == [0x40,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src as u256,dst as u256,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x40,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MLoad(st);
		//|fp=0x0060|0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,2);
		//|fp=0x0060|0x60,wad,0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x09c1(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x09c1(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09c1
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x60) == wad
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires st'.evm.stack.contents == [0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src as u256,dst as u256,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(11)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,2);
		//|fp=0x0060|wad,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x09ce(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x09ce(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09ce
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	requires st'.evm.stack.contents == [0x60,0x20,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src as u256,dst as u256,0x0,wad,dst as u256,src as u256,0x229,st'.Peek(10)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x20,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src*,dst*,0x0,wad,dst*,src*,0x229,transferFrom|
		st := LogN(st,3);
		//|fp=0x0060|0x00,wad,dst*,src*,0x229,transferFrom|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,0x00,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x0,0x01,wad,dst*,src*,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x01,wad,dst*,src*,0x229,transferFrom|
		st := Swap(st,4);
		//|fp=0x0060|0x229,wad,dst*,src*,0x01,transferFrom|
		st := Swap(st,3);
		//|fp=0x0060|src*,wad,dst*,0x229,0x01,transferFrom|
		st := Pop(st);
		//|fp=0x0060|wad,dst*,0x229,0x01,transferFrom|
		st := Pop(st);
		//|fp=0x0060|dst*,0x229,0x01,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x09d7(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x09d7(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09d7
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	requires st'.evm.stack.contents == [dst as u256,0x229,0x01,st'.Peek(3)] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|dst*,0x229,0x01,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x229,0x01,transferFrom|
		assume {:axiom} st.IsJumpDest(0x229);
		st := Jump(st);
		st := block_0_0x0229(dBal,bal,src,dst,wad,callSig,st); 
		return st;
	}

	
	
}
