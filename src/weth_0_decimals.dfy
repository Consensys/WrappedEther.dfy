include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module decimals {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x0266(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0266
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires callSig == 0x313ce567 
	requires st'.evm.stack.contents == [callSig]
	// Storage
	requires st'.Load(0x02) == 18 // uint8  public decimals = 18.

	ensures st'.evm.context.callValue != 0 ==> st''.IsRevert()
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|decimals|
		st := JumpDest(st);
		//|fp=0x0060|decimals|
		st := CallValue(st);
		//|fp=0x0060|callVal,decimals|
		st := IsZero(st);
		//|fp=0x0060|callVal==0,decimals|
		st := Push2(st,0x0271);
		//|fp=0x0060|0x271,callVal==0,decimals|
		assume {:axiom} st.IsJumpDest(0x271);
		st := JumpI(st);
		if st.PC() == 0x271 { 
			// callVal==0
			stackLemma(st,st.Operands());
			st := block_0_0x0271(callSig,st); 
			return st;
		}
		//|fp=0x0060|decimals|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,decimals|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,decimals|
		st := Revert(st); //i.e. revert if call value != 0 
		return st;
	}

	method block_0_0x0271(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0271
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires st'.evm.stack.contents == [callSig]
	requires callSig == 0x313ce567 && st'.evm.context.callValue == 0
	// Storage
	requires st'.Load(0x02) == 18 // uint8  public decimals = 18.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|decimals|
		st := JumpDest(st);
		//|fp=0x0060|decimals|
		st := Push2(st,0x0279);
		//|fp=0x0060|0x279,decimals|
		st := Push2(st,0x0b05);
		//|fp=0x0060|0xb05,0x279,decimals|
		assume {:axiom} st.IsJumpDest(0xb05);
		st := Jump(st);
		st := block_0_0x0b05(callSig,st);
		return st;
	}

	method block_0_0x0279(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0279
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	requires st'.evm.stack.contents == [0x12,st'.Peek(1),callSig]
	requires callSig == 0x313ce567 && st'.evm.context.callValue == 0
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x12,0x279,decimals|
		st := JumpDest(st);
		//|fp=0x0060|0x12,0x279,decimals|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x12,0x279,decimals|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x12,0x279,decimals|
		//assert (st.Peek(0) == 0x60 && st.Peek(1) == 0x12);
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x12,0x279,decimals|
		st := Dup(st,3);
		//|fp=0x0060|0x12,0x60,0x60,0x12,0x279,decimals|
		st := Push1(st,0xff);
		//|fp=0x0060|0xff,0x12,0x60,0x60,0x12,0x279,decimals|
		st := AndU8(st);
		//|fp=0x0060|0x12,0x60,0x60,0x12,0x279,decimals|
		st := Push1(st,0xff);
		stackLemma(st,st.Operands());
		st := block_0_0x0284(callSig,st);
		return st;
	}

	method block_0_0x0284(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0284
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	requires st'.evm.stack.contents == [0xff,0x12,0x60,0x60,0x12,st'.Peek(5),callSig]
	requires callSig == 0x313ce567 && st'.evm.context.callValue == 0
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xff,0x12,0x60,0x60,0x12,0x279,decimals|
		st := AndU8(st);
		//|fp=0x0060|0x12,0x60,0x60,0x12,0x279,decimals|
		assert st.Peek(0)==0x12;
		st := Dup(st,2);
		//|fp=0x0060|0x60,0x12,0x60,0x60,0x12,0x279,decimals|
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0287(callSig,st);
		return st;
	}

	method block_0_0x0287(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0287
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60 && st'.Read(0x60) == 0x12
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires st'.evm.stack.contents == [0x60,0x60,0x12,st'.Peek(3),callSig]
	requires callSig == 0x313ce567 && st'.evm.context.callValue == 0
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x60,0x12,0x279,decimals|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,0x12,0x279,decimals|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,0x60,0x60,0x12,0x279,decimals|
		st := Add(st);
		assert st.Peek(0) == 0x80;
		//|fp=0x0060|0x80,0x60,0x12,0x279,decimals|
		st := Swap(st,2);
		//|fp=0x0060|0x12,0x60,0x80,0x279,decimals|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0x279,decimals|
		st := Pop(st);
		//|fp=0x0060|0x80,0x279,decimals|
		stackLemma(st,st.Operands());
		st := block_0_0x028d(callSig,st);
		return st;
	}

	method block_0_0x028d(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x028d
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60 && st'.Read(0x60) == 0x12
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires st'.evm.stack.contents == [0x80,st'.Peek(1),callSig]
	requires callSig == 0x313ce567 && st'.evm.context.callValue == 0

	ensures st''.RETURNS? && st''.data == Int.ToBytes(0x12) 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x80,0x279,decimals|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0x279,decimals|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0x279,decimals|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0x279,decimals|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,0x279,decimals|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,0x279,decimals|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0x279,decimals|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0x279,decimals|
		MemoryReadAxiom(st,0x60);
		st := Return(st);
		return st;
	}

	method block_0_0x0b05(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b05
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires st'.evm.stack.contents == [0x279,callSig]
	requires callSig == 0x313ce567 && st'.evm.context.callValue == 0

	requires st'.Load(0x02) == 18 // uint8  public decimals = 18.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x279,decimals|
		st := JumpDest(st);
		//|fp=0x0060|0x279,decimals|
		st := Push1(st,0x02);
		//|fp=0x0060|0x02,0x279,decimals|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x02,0x279,decimals|
		st := Swap(st,1);
		//|fp=0x0060|0x02,0x00,0x279,decimals|
		st := SLoad(st);
		//|fp=0x0060|st.Load(0x02)=18,0x00,0x279,decimals|
		st := Swap(st,1);
		//|fp=0x0060|0x00,st.Load(0x02)=18,0x279,decimals|
		st := Push2(st,0x0100);
		//|fp=0x0060|0x100,0x00,st.Load(0x02)=18,0x279,decimals|
		//assert st.Peek(0) == 0x100 && st.Peek(1) == 0x00;
		st := Exp(st);
		//|fp=0x0060|0x1,st.Load(0x02)=18,0x279,decimals|
		//assert st.Peek(0) == 0x01;
		stackLemma(st,st.Operands());
		st := block_0_0x0b11(callSig,st);
		return st;
	}

	method block_0_0x0b11(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b11
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires st'.evm.stack.contents == [0x01,0x12,0x279,callSig]
	requires callSig == 0x313ce567 && st'.evm.context.callValue == 0

	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x1,0x12,0x279,decimals|
		st := Swap(st,1);
		//|fp=0x0060|0x12,0x1,0x279,decimals|
		assert st.Peek(1) != 0;
		st := Div(st);
		//|fp=0x0060|0x12,0x279,decimals|
		st := Push1(st,0xff);
		//|fp=0x0060|0xff,0x12,0x279,decimals|
		st := AndU8(st);
		//|fp=0x0060|0x12,0x279,decimals|
		//assert st.Peek(0) == 0x12;
		st := Dup(st,2);
		//|fp=0x0060|0x279,0x12,0x279,decimals|
		assume {:axiom} st.IsJumpDest(0x279);
		st := Jump(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0279(callSig,st);
		return st;
	}

}
