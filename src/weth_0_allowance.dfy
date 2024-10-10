include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module allowance {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header
	import opened Int

	// from block_0_0x00a3 in main
	method block_0_0x03d4(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03d4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires 0xdd62ed3e == callSig
	requires st'.evm.stack.contents == [callSig]

	ensures st'.evm.context.callValue != 0 ==> st''.IsRevert()
	
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
		st := Push2(st,0x03df);
		//|fp=0x0060|0x3df,_,_|
		assume {:axiom} st.IsJumpDest(0x3df);
		st := JumpI(st);
		if st.PC() == 0x3df { 
			// call value is zero
			stackLemma(st,st.Operands());
			st := block_0_0x03df(callSig,st); 
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

	method block_0_0x03df(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03df
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires 0xdd62ed3e == callSig
	requires st'.evm.stack.contents == [callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
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
		var addr1 := st.Peek(0) as u160;
		assert addr1 as u256 == st.evm.context.CallDataRead(0x04) % (Int.TWO_160 as u256);
		stackLemma(st,st.Operands());
		st := block_0_0x03fe(addr1,callSig,st);
		return st;
	}

	method block_0_0x03fe(addr1: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03fe
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [addr1 as u256,0x4,0x4,0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|addr1,0x04,0x04,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|0x04,addr1,0x04,0x42a,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,addr1,0x04,0x42a,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		//|fp=0x0060|0x20,0x04,addr1,0x04,0x42a,_|
		st := Add(st);
		//|fp=0x0060|0x24,addr1,0x04,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|addr1,0x24,0x04,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,addr1,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,addr1,0x42a,_|
		st := Dup(st,1);
		//|fp=0x0060|0x24,0x24,0x04,addr1,0x42a,_|
		st := CallDataLoad(st);
		//|fp=0x0060|callData(0x24),0x24,0x04,addr1,0x42a,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0407(addr1,callSig,st);
		return st;
	}

	method block_0_0x0407(addr1: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0407
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [st'.evm.context.CallDataRead(0x24),0x24,0x04,addr1 as u256,0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|callData(0x24),0x24,0x04,addr1,0x42a,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x24,0x04,_,0x42a,_|
		stackLemma(st,st.Operands());
		st := AndU160(st);
		var addr2 := st.Peek(0) as u160;
		assert addr2 as u256 == st.evm.context.CallDataRead(0x24) % (Int.TWO_160 as u256) ;
		//|fp=0x0060|addr2,0x24,0x04,addr1,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24,addr2,0x04,addr1,0x42a,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x24,addr2,0x04,addr1,0x42a,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		//|fp=0x0060|0x20,0x24,addr2,0x04,addr1,0x42a,_|
		st := Add(st);
		//|fp=0x0060|0x44,addr2,0x04,addr1,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|addr2,0x44,0x04,addr1,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x44,addr2,addr1,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|0x44,0x04,addr2,addr1,0x42a,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0424(addr1,addr2,callSig,st);
		return st;
	}

	method block_0_0x0424(addr1: u160, addr2: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0424
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [st'.Peek(0),st'.Peek(1),addr2 as u256,addr1 as u256,0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x44,0x04,addr2,addr1,0x42a,_|
		st := Pop(st);
		//|fp=0x0060|0x04,addr2,addr1,0x42a,_|
		st := Pop(st);
		//|fp=0x0060|addr2,addr1,0x42a,_|
		st := Push2(st,0x0be3);
		//|fp=0x0060|0xbe3,addr2,addr1,0x42a,_|
		assume {:axiom} st.IsJumpDest(0xbe3);
		st := Jump(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0be3(addr1,addr2,callSig,st);
		return st;
	}

	method block_0_0x042a(allowance: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x042a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [allowance,st'.Peek(1),callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|allowance,0x42a,_|
		st := JumpDest(st);
		//|fp=0x0060|allowance,0x42a,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,allowance,0x42a,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,allowance,0x42a,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,allowance,0x42a,_|
		st := Dup(st,3);
		//|fp=0x0060|allowance,0x60,0x60,allowance,0x42a,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,allowance,0x60,0x60,allowance,0x42a,_|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,allowance,0x42a,_| i.e. st.Read(0x60) == allowance
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,allowance,0x42a,_| 
		stackLemma(st,st.Operands());
		st := block_0_0x0434(allowance,callSig,st);
		return st;
	}

	method block_0_0x0434(allowance: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0434
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60 && st'.Read(0x60) == allowance
	// Stack height(s)
	requires st'.Operands() == 6
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [0x20,0x60,0x60,allowance,st'.Peek(4),callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x60,0x60,allowance,0x42a,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,allowance,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|alllowance,0x60,0x80,0x42a,_|
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
		//|fp=0x0060|0x80,0x60,0x60,0x42a,_|
		stackLemma(st,st.Operands());
		st := block_0_0x043d(allowance,callSig,st);
		return st;
	}

	method block_0_0x043d(allowance: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x043d
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60  && st'.Read(0x60) == allowance
	// Stack height(s)
	requires st'.Operands() == 5
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [0x80,0x60,0x60,st'.Peek(3),callSig]
	
	ensures st''.RETURNS? && st''.data == Int.ToBytes(allowance as nat) // Memory.Slice(st'.evm.memory, 0x60, 0x20)
	
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x80,0x60,0x60,0x42a,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,0x42a,_|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0x42a,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0x42a,_|
		//assume {:axiom} Memory.Slice(st.evm.memory, 0x60, 0x20) == Int.ToBytes(st.Read(0x60) as nat);
		MemoryReadAxiom(st,0x60);
		st := Return(st);
		return st;
	}

	method block_0_0x0be3(addr1: u160, addr2: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0be3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [addr2 as u256,addr1 as u256,0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|addr2,addr1,0x42a,_|
		st := JumpDest(st);
		//|fp=0x0060|addr2,addr1,0x42a,_|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,addr2,addr1,0x42a,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,addr2,addr1,0x42a,_|
		st := MStore(st);
		//|fp=0x0060|addr2,addr1,0x42a,_| i.e. st.Read(0x20) == 0x04
		stackLemma(st,st.Operands());
		st := block_0_0x0be9(addr1,addr2,callSig,st);
		return st;
	}

	method block_0_0x0be9(addr1: u160, addr2: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0be9
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == 0x04 
	// Stack height(s)
	requires st'.Operands() == 4
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [addr2 as u256,addr1 as u256,0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Dup(st,2);
		//|fp=0x0060|addr1,addr2,addr1,0x42a,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,addr1,addr2,addr1,0x42a,_|
		st := MStore(st);
		//|fp=0x0060|addr2,addr1,0x42a,_| i.e. st.Read(0x00) == addr1
		stackLemma(st,st.Operands());
		st := block_0_0x0bed(addr1,addr2,callSig,st);
		return st;
	}

	method block_0_0x0bed(addr1: u160, addr2: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bed
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == addr1 as u256 && st'.Read(0x20) == 0x04
	// Stack height(s)
	requires st'.Operands() == 4
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [addr2 as u256,addr1 as u256,0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|addr2,addr1,0x42a,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,addr2,addr1,0x42a,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,addr2,addr1,0x42a,_|
		st := Keccak256(st);
		//|fp=0x0060|hash[addr1,0x04],addr2,addr1,0x42a,_|
		HashEquivalenceAxiom(st,st.Peek(0),addr1 as u256,0x04);
		assert st.Peek(0) == Hash(addr1 as u256,0x04);
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,hash[addr1,0x04],addr2,addr1,0x42a,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0bf4(addr1,addr2,callSig,st);
		return st;
	}

	method block_0_0x0bf4(addr1: u160, addr2: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bf4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 
	// Stack height(s)
	requires st'.Operands() == 6
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [0x20,Hash(addr1 as u256,0x04),addr2 as u256,st'.Peek(3),0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,hash[addr1,0x04],addr2,addr1,0x42a,_|
		st := MStore(st);
		//|fp=0x0060|addr2,addr1,0x42a,_| i.e. st.Read(0x20) == hash[addr1,0x04]
		stackLemma(st,st.Operands());
		st := block_0_0x0bf5(addr1,addr2,callSig,st);
		return st;
	}


	method block_0_0x0bf5(addr1: u160, addr2: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bf5
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == Hash(addr1 as u256,0x04)
	// Stack height(s)
	requires st'.Operands() == 4
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [addr2 as u256,st'.Peek(1),0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Dup(st,1);
		//|fp=0x0060|addr2,addr2,addr1,0x42a,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,addr2,addr2,addr1,0x42a,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0bf8(addr1,addr2,callSig,st);
		return st;
	}

	method block_0_0x0bf8(addr1: u160, addr2: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bf8
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == Hash(addr1 as u256,0x04)
	// Stack height(s)
	requires st'.Operands() == 6
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [0x0,addr2 as u256,addr2 as u256,st'.Peek(3),0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x00,addr2,addr2,addr1,0x42a,_|
		st := MStore(st);
		//assert st.Read(0x40) == 0x60;
		//|fp=0x0060|addr2,addr1,0x42a,_|  i.e. st.Read(0x00) == addr2
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,addr2,addr1,0x42a,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0bfb(addr1,addr2,callSig,st);
		return st;
	}

	method block_0_0x0bfb(addr1: u160, addr2: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bfb
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == addr2 as u256 && st'.Read(0x20) == Hash(addr1 as u256,0x04)
	// Stack height(s)
	requires st'.Operands() == 5
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [0x40,addr2 as u256,st'.Peek(2),0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x40,addr2,addr1,0x42a,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,addr2,addr1,0x42a,_|
		st := Keccak256(st);
		//|fp=0x0060|hash[addr2,hash1],addr2,addr1,0x42a,_
		HashEquivalenceAxiom(st,st.Peek(0),addr2 as u256,Hash(addr1 as u256,0x04));
		assert st.Peek(0) == Hash(addr2 as u256,Hash(addr1 as u256,0x04));
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash[addr2,hash1],addr2,addr1,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|addr2,hash[addr2,hash1],0x00,addr1,0x42a,_|
		st := Pop(st);
		//|fp=0x0060|hash[addr2,hash1],0x00,addr1,0x42a,_|
		st := Swap(st,2);
		//|fp=0x0060|addr1,0x00,hash[addr2,hash1],0x42a,_|
		st := Pop(st);
		//|fp=0x0060|0x00,hash[addr2,hash1],0x42a,_|
		st := Pop(st);
		//|fp=0x0060|hash[addr2,hash1],0x42a,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0c05(addr1,addr2,callSig,st);
		return st;
	}

	method block_0_0x0c05(addr1: u160, addr2: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0c05
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	requires 0xdd62ed3e == callSig
	// Static stack items
	requires st'.evm.stack.contents == [Hash(addr2 as u256,Hash(addr1 as u256,0x04)),0x42a,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|hash[addr2,hash1],0x42a,_|
		st := SLoad(st);
		//|fp=0x0060|allowance[addr1,addr2],0x42a,_|
		var allowance := st.Peek(0);
		assert allowance == st.Load(Hash(addr2 as u256,Hash(addr1 as u256,0x04)));
		st := Dup(st,2);
		//|fp=0x0060|0x42a,allowance,0x42a,_|
		assume {:axiom} st.IsJumpDest(0x42a);
		st := Jump(st);
		stackLemma(st,st.Operands());
		st := block_0_0x042a(allowance,callSig,st);
		return st;
	}

}
