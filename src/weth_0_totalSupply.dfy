include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module totalSupply {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x01a1(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01a1
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	// Stack
	requires 0x18160ddd == callSig
	requires st'.evm.stack.contents == [callSig]

	ensures st'.evm.context.callValue != 0 ==> st''.IsRevert()
	
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := CallValue(st);
		//|fp=0x0060|_,_|
		st := IsZero(st);
		//|fp=0x0060|_,_|
		st := Push2(st,0x01ac);
		//|fp=0x0060|0x1ac,_,_|
		assume {:axiom} st.IsJumpDest(0x1ac);
		st := JumpI(st);
		if st.PC() == 0x1ac { st := block_0_0x01ac(callSig,st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x01ac(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01ac
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	// Stack
	requires callSig == 0x18160ddd
	requires st'.evm.stack.contents == [callSig]
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x01b4);
		//|fp=0x0060|0x1b4,_|
		st := Push2(st,0x066d);
		//|fp=0x0060|0x66d,0x1b4,_|
		assume {:axiom} st.IsJumpDest(0x66d);
		st := Jump(st);
		st := block_0_0x066d(callSig,st);
		return st;
	}

	method block_0_0x01b4(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01b4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Stack
	requires callSig == 0x18160ddd
	requires st'.evm.stack.contents == [st'.evm.world.Balance(st'.evm.context.address),callSig]
	{
		var st := st';
		//|fp=0x0060|st.evm.world.Balance(st.evm.context.address),_|
		st := JumpDest(st);
		//|fp=0x0060|st.evm.world.Balance(st.evm.context.address),_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,st.evm.world.Balance(st.evm.context.address),_|
		st := MLoad(st);
		//|fp=0x0060|0x60,st.evm.world.Balance(st.evm.context.address),_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,st.evm.world.Balance(st.evm.context.address),_|
		st := Dup(st,3);
		//|fp=0x0060|st.evm.world.Balance(st.evm.context.address),0x60,0x60,st.evm.world.Balance(st.evm.context.address),_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,st.evm.world.Balance(st.evm.context.address),0x60,0x60,st.evm.world.Balance(st.evm.context.address),_|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,st.evm.world.Balance(st.evm.context.address),_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,st.evm.world.Balance(st.evm.context.address),_|
		st := block_0_0x01be(callSig,st);
		return st;
	}

	method block_0_0x01be(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01be
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60 && st'.Read(0x60) ==st'.evm.world.Balance(st'.evm.context.address)
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires callSig == 0x18160ddd
	requires st'.evm.stack.contents == [0x20,0x60,st'.Peek(2),st'.Peek(3),callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x60,0x60,st.evm.world.Balance(st.evm.context.address),_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,st.evm.world.Balance(st.evm.context.address),_|
		st := Swap(st,2);
		//|fp=0x0060|st.evm.world.Balance(st.evm.context.address),0x60,0x80,_|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,_|
		st := Pop(st);
		//|fp=0x0060|0x80,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,_|
		st := Swap(st,2);
		stackLemma(st,st.Operands());
		st := block_0_0x01c7(callSig,st);
		return st;
	}

	method block_0_0x01c7(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01c7
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60 && st'.Read(0x60) == st'.evm.world.Balance(st'.evm.context.address)
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires callSig == 0x18160ddd
	requires st'.evm.stack.contents == [0x80,0x60,0x60,callSig]
	
	ensures st''.RETURNS? 
			&& st''.world.Exists(st'.evm.context.address) 
			&& st''.data == Int.ToBytes(st'.evm.world.Balance(st'.evm.context.address) as nat) 
	{
		var st := st';
		var ts := st.evm.world.Balance(st.evm.context.address);
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x80,0x60,0x60,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,_|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,_|
		MemoryReadAxiom(st,0x60);
		st := Return(st);
		return st;
	}

	method block_0_0x066d(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x066d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires callSig == 0x18160ddd
	requires st'.evm.stack.contents == [0x1b4,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x1b4,_|
		st := JumpDest(st);
		//|fp=0x0060|0x1b4,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x1b4,_|
		st := Address(st);
		//|fp=0x0060|st.evm.context.address,0x00,0x1b4,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,st.evm.context.address,0x00,0x1b4,_|
		st := AndU160(st);
		//|fp=0x0060|st.evm.context.address,0x00,0x1b4,_|
		st := Balance(st);
		//|fp=0x0060|st.evm.world.Balance(st.evm.context.address),0x00,0x1b4,_|
		st := Swap(st,1);
		//|fp=0x0060|0x00,st.evm.world.Balance(st.evm.context.address),0x1b4,_|
		st := Pop(st);
		stackLemma(st,st.Operands());
		st := block_0_0x068a(callSig,st);
		return st;
	}

	method block_0_0x068a(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x068a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires callSig == 0x18160ddd
	requires st'.evm.stack.contents == [st'.evm.world.Balance(st'.evm.context.address),0x1b4,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|_,0x1b4,_|
		st := Swap(st,1);
		//|fp=0x0060|0x1b4,_,_|
		assume {:axiom} st.IsJumpDest(0x1b4);
		st := Jump(st);
		stackLemma(st,st.Operands());
		st := block_0_0x01b4(callSig,st);
		return st;
	}

}
