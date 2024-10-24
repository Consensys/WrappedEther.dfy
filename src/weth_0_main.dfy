include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"
include "weth_0_transfer.dfy"
include "weth_0_balanceOf.dfy"
include "weth_0_allowance.dfy"
include "weth_0_decimals.dfy"
include "weth_0_deposit.dfy"
include "weth_0_symbol.dfy"
include "weth_0_name.dfy"
include "weth_0_approve.dfy"
include "weth_0_totalSupply.dfy"
include "weth_0_util.dfy"

module main {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header
	import opened transfer
	import opened balanceOf
	import opened allowance
	import opened decimals
	import opened deposit
	import opened symbol
	import opened name
	import opened approve
	import opened totalSupply
	import opened util
	import opened Int

	method block_0_0x0000(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0000
	// Stack height(s)
	requires st'.Operands() == 0
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	requires st'.Load(0x02) == 18 // uint8  public decimals = 18.
	{
		var st := st';
		//|fp=0x0000||
		st := Push1(st,0x60);
		//|fp=0x0000|0x60|
		st := Push1(st,0x40);
		//|fp=0x0000|0x40,0x60|
		st := MStore(st);
		//|fp=0x0060||
		st := Push1(st,0x04);
		//|fp=0x0060|0x04|
		st := CallDataSize(st);
		//|fp=0x0060|cdSize,0x04|
		st := Lt(st);
		//|fp=0x0060|{0,1}|
		st := Push2(st,0x00af);
		//|fp=0x0060|0xaf,{0,1}|
		assume {:axiom} st.IsJumpDest(0xaf);
		st := JumpI(st);
		if st.PC() == 0xaf {st := block_0_0x00af(0,st); return st;} // call data size < 0x04
		// call data size >= 0x04
		st := block_0_0x000d(st);
		return st;
	}

	method block_0_0x000d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x000d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 0
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	requires st'.Load(0x02) == 18 // uint8  public decimals = 18.
	{
		// implies calll data size >=  4 bytes
		var st := st';
		//|fp=0x0060||
		st := Push1(st,0x00);
		//|fp=0x0060|0x00|
		st := CallDataLoad(st);
		//|fp=0x0060|cData[0x00]|
		st := PushN(st,29,0x0100000000000000000000000000000000000000000000000000000000);
		//|fp=0x0060|0x100000000000000,cData[0x00]|
		st := Swap(st,1);
		//|fp=0x0060|cData[0x00],0x100000000000000|
		assert st.Peek(1) != 0;
		st := Bytecode.Div(st);
		//|fp=0x0060|_|
		st := Push4(st,0xffffffff);
		//|fp=0x0060|0xffffffff,_|
		st := AndU32(st);
		//|fp=0x0060|callSig|
		var callSig := st.Peek(0);
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig| // first 4 bytes of call data
		st := block_0_0x0037(callSig,st);
		return st;
	}

	method block_0_0x0037(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0037
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Stack 
	requires st'.evm.stack.contents == [callSig,callSig]
	// Storage
	requires st'.Load(0) == 0x577261707065642045746865720000000000000000000000000000000000001a // length of "Wrapped Ether", shifted left.
	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	requires st'.Load(0x02) == 18 // uint8  public decimals = 18.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x06fdde03);
		//|fp=0x0060|0x6fdde03,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x6fdde03==callSig,callSig|
		st := Push2(st,0x00b9);
		//|fp=0x0060|0xb9,0x6fdde03==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0xb9);
		st := JumpI(st);
		if st.PC() == 0xb9 { st := block_0_0x00b9(callSig,st); return st;} // fn 0x6fdde03 i.e. name()
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x095ea7b3);
		//|fp=0x0060|0x95ea7b3,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x95ea7b3==callSig,callSig|
		st := Push2(st,0x0147);
		//|fp=0x0060|0x0147,0x95ea7b3==callSig,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x004b(callSig,st);
		return st;
	}

	method block_0_0x004b(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x004b
	requires callSig !in {0x6fdde03}
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Stack items
	requires st'.Peek(1) == if 0x95ea7b3==callSig then 1 else 0
	requires st'.evm.stack.contents == [0x147,st'.Peek(1),callSig]
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	requires st'.Load(0x02) == 18 // uint8  public decimals = 18.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0147,0x95ea7b3==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x147);
		st := JumpI(st);
		if st.PC() == 0x147 { // fn 0x95ea7b3 i.e. approve(address,uint256)
			stackLemma(st,st.Operands());
			st := block_0_0x0147(callSig,st); 
			return st;
		}  
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x18160ddd);
		//|fp=0x0060|0x18160ddd,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x18160ddd==callSig,callSig|
		st := Push2(st,0x01a1);
		//|fp=0x0060|0x1a1,0x18160ddd==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x1a1);
		st := JumpI(st);
		if st.PC() == 0x1a1 { // fn 0x18160ddd i.e. totalSupply()
			//assert callSig == 0x18160ddd;
			stackLemma(st,st.Operands());
			st := block_0_0x01a1(callSig,st); 
			return st;
		} 
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x23b872dd);
		//|fp=0x0060|0x23b872dd,callSig,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x005d(callSig,st);
		return st;
	}

	method block_0_0x005d(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x005d
	requires callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd}
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	requires st'.evm.stack.contents == [0x23b872dd,callSig,callSig]
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	requires st'.Load(0x02) == 18 // uint8  public decimals = 18.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x23b872dd,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x23b872dd==callSig,callSig|
		st := Push2(st,0x01ca);
		//|fp=0x0060|0x1ca,0x23b872dd==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x1ca);
		st := JumpI(st);
		if st.PC() == 0x1ca { // fn 0x23b872dd i.e. transferFrom(address,address,uint256)
			stackLemma(st,st.Operands());
			st := block_0_0x01ca(callSig,st); 
			return st;
		}
		stackLemma(st,st.Operands());
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x2e1a7d4d);
		//|fp=0x0060|0x2e1a7d4d,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x2e1a7d4d==callSig,callSig|
		st := Push2(st,0x0243);
		//|fp=0x0060|0x243,0x2e1a7d4d==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x243);
		st := JumpI(st);
		assert st.evm.stack.contents == [callSig];
		if st.PC() == 0x243 { // fn 0x2e1a7d4d ie. withdraw(uint256)
			stackLemma(st,st.Operands());
			st := block_0_0x0243(callSig,st); 
			return st;
		} 
		//|fp=0x0060|callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x006d(callSig,st);
		return st;
	}

	method block_0_0x006d(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x006d
	requires callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d}
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires st'.evm.stack.contents == [callSig]
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	requires st'.Load(0x02) == 18 // uint8  public decimals = 18.
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x313ce567);
		//|fp=0x0060|0x313ce567,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x313ce567==callSig,callSig|
		st := Push2(st,0x0266);
		//|fp=0x0060|0x266,0x313ce567==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x266);
		st := JumpI(st);
		if st.PC() == 0x266 { // fn 0x313ce567 i.e. decimals()
			//stackLemma(st,st.Operands());
			st := block_0_0x0266(callSig,st); 
			return st;
		} 
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x70a08231);
		//|fp=0x0060|0x70a08231,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x70a08231==callSig,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x007f(callSig,st);
		return st;
	}

	method block_0_0x007f(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x007f
	requires callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567}
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	requires st'.Peek(0) == if 0x70a08231 == callSig then 1 else 0
	requires st'.evm.stack.contents == [st'.Peek(0),callSig]
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x70a08231==callSig,callSig|
		st := Push2(st,0x0295);
		//|fp=0x0060|0x295,0x70a08231==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x295);
		st := JumpI(st);
		if st.PC() == 0x295 { // fn 0x70a08231 ie. balanceOf(address)
			stackLemma(st,st.Operands());
			st := block_0_0x0295(callSig,st); 
			return st;
		} 
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x95d89b41);
		//|fp=0x0060|0x95d89b41,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x95d89b41==callSig,callSig|
		st := Push2(st,0x02e2);
		//|fp=0x0060|0x2e2,0x95d89b41==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x2e2);
		st := JumpI(st);
		if st.PC() == 0x2e2 { // fn 0x95d89b41 i.e. symbol()
			stackLemma(st,st.Operands());
			st := block_0_0x02e2(callSig,st); 
			return st;
		} 
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x008f(callSig,st);
		return st;
	}

	method block_0_0x008f(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x008f
	requires callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41}
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	requires st'.evm.stack.contents == [callSig,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0xa9059cbb);
		//|fp=0x0060|0xa9059cbb,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0xa9059cbb==callSig,callSig|
		st := Push2(st,0x0370);
		//|fp=0x0060|0x370,0xa9059cbb==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x370);
		st := JumpI(st);
		if st.PC() == 0x370 { //i.e. fn 0xa9059cbb transfer(address,uint256)
			stackLemma(st,st.Operands());
			st := block_0_0x0370(callSig,st); 
			return st;
		} 
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0xd0e30db0);
		//|fp=0x0060|0xd0e30db0,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0xd0e30db0==callSig,callSig|
		st := Push2(st,0x03ca);
		//|fp=0x0060|0x03ca,0xd0e30db0==callSig,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x00a3(callSig,st);
		return st;
	}

	method block_0_0x00a3(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00a3
	requires callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb}
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Stack items
	requires st'.Peek(1) == if 0xd0e30db0 == callSig then 1 else 0
	requires st'.evm.stack.contents == [0x3ca,st'.Peek(1),callSig]
	requires st'.evm.stack.contents[0] == 0x3ca
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x03ca,0xd0e30db0==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x3ca);
		st := JumpI(st);
		if st.PC() == 0x3ca { // i.e. fn 0xd0e30db0 deposit()
			stackLemma(st,st.Operands());
			st := block_0_0x03ca(callSig,st); 
			return st;
		}  
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0xdd62ed3e);
		//|fp=0x0060|0xdd62ed3e,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0xdd62ed3e==callSig,callSig|
		st := Push2(st,0x03d4);
		//|fp=0x0060|0x3d4,0xdd62ed3e==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x3d4);
		st := JumpI(st);
		if st.PC() == 0x3d4 { // fn 0xdd62ed3e allowance(address,address)
			stackLemma(st,st.Operands());
			st := block_0_0x03d4(callSig,st); 
			return st;
		} 
		//|fp=0x0060|callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x00af(callSig,st);
		return st;
	}

	method block_0_0x00af(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00af
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() >= 0 && st'.Operands() <= 1
	requires st'.evm.stack.contents == []  || st'.evm.stack.contents == [callSig]

	requires st'.Operands() == 0 ==> st'.evm.context.CallDataSize() < 0x04
	requires st'.Operands() == 1 ==> callSig !in {0x6fdde03,0x95ea7b3,0x18160ddd,0x23b872dd,0x2e1a7d4d,0x313ce567,0x70a08231,0x95d89b41,0xa9059cbb,0xd0e30db0,0xdd62ed3e}
	{
		var st := st';	
		// from a3: |fp=0x0060|callSig|
		// from 00: |fp=0x0060||
		st := JumpDest(st);
		// from a3: |fp=0x0060|callSig|
		// from 00: |fp=0x0060||
		st := Push2(st,0x00b7);
		// from a3: |fp=0x0060|0x00b7,callSig|
		// from 00: |fp=0x0060|0x00b7|
		st := Push2(st,0x0440);
		// from a3: |fp=0x0060|0x0440,0x00b7,callSig|
		// from 00: |fp=0x0060|0x0440,0x00b7|
		assume {:axiom} st.IsJumpDest(0x440);
		st := Jump(st);
		// from a3: |fp=0x0060|0x00b7,callSig|
		// from 00: |fp=0x0060|0x00b7|
		if st.Operands() == 2 {
			stackLemma(st,st.Operands());
			st := block_1_0x0440(callSig,st);
			}
		else {
			stackLemma(st,st.Operands());
			st := block_0_0x0440(st);
		}
		return st;
	}

	method block_0_0x01ca(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01ca
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires callSig == 0x23b872dd
	requires st'.evm.stack.contents == [callSig]

	ensures st'.evm.context.callValue != 0 ==> st''.IsRevert()
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|transferFrom|
		st := JumpDest(st);
		//|fp=0x0060|transferFrom|
		st := CallValue(st);
		//|fp=0x0060|callVal,transferFrom|
		st := IsZero(st);
		//|fp=0x0060|callVal==0,transferFrom|
		st := Push2(st,0x01d5);
		//|fp=0x0060|0x1d5,callVal==0,transferFrom|
		assume {:axiom} st.IsJumpDest(0x1d5);
		st := JumpI(st);
		if st.PC() == 0x1d5 { 
			stackLemma(st,st.Operands());
			assert st.evm.context.callValue == 0 ;
			st := block_0_0x01d5(callSig,st); 
			return st;
		} // call value is zero
		//|fp=0x0060|transferFrom|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,transferFrom|
		st := Revert(st);
		return st;
	}

	method block_0_0x01d5(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01d5
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1

	requires st'.evm.stack.contents == [callSig]
	requires callSig == 0x23b872dd
	
	requires st'.evm.context.callValue == 0
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|transferFrom|
		st := JumpDest(st);
		//|fp=0x0060|transferFrom|
		st := Push2(st,0x0229);
		//|fp=0x0060|0x229,transferFrom|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,0x229,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x229,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x04,0x229,transferFrom|
		st := CallDataLoad(st);
		//|fp=0x0060|src,0x04,0x04,0x229,transferFrom| i.e. address from callData[4] == parm0 == src addr
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,src,0x04,0x04,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|src,0x04,0x04,0x229,transferFrom|  
		var src := st.Peek(0) as u160;
		assert src as u256 == st.evm.context.CallDataRead(0x04) % (Int.TWO_160 as u256);
		stackLemma(st,st.Operands());
		st := block_0_0x01f4(src,callSig,st);
		return st;
	}

	method block_0_0x01f4(src: u160,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01f4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Stack items
	requires st'.evm.stack.contents == [src as u256,0x4,0x4,0x229,callSig]
	requires callSig == 0x23b872dd
	
	requires st'.evm.context.callValue == 0
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|src,0x04,0x04,0x229,transferFrom|  
		st := Swap(st,1);
		//|fp=0x0060|0x04,src,0x04,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,src,0x04,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x24,src,0x04,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|src,0x24,0x04,0x229,transferFrom|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,src,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,src,0x229,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x24,0x24,0x04,src,0x229,transferFrom|
		st := CallDataLoad(st);
		//|fp=0x0060|callData[0x24],0x24,0x04,src,0x229,transferFrom| i.e. address from callData[0x24] == parm1 == dst addr
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents[0..5] == [st.evm.context.CallDataRead(0x24),0x24,0x04,src as u256,0x229];
		st := block_0_0x01fd(src,callSig,st);
		return st;
	}

	method block_0_0x01fd(src: u160,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01fd
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Stack items
	requires st'.evm.stack.contents == [st'.evm.context.CallDataRead(0x24),0x24,0x04,src as u256,0x229,callSig]
	requires callSig == 0x23b872dd
	
	requires st'.evm.context.callValue == 0
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|callData[0x24],0x24,0x04,src,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,dst,0x24,0x04,src,0x229,transferFrom|
		//stackLemma(st,st.Operands());
		st := AndU160(st);
		//|fp=0x0060|dst,0x24,0x04,src,0x229,transferFrom| 
		var dst := st.Peek(0) as u160;
		assert dst as u256 == st.evm.context.CallDataRead(0x24) % (Int.TWO_160 as u256);
		assert st.Peek(4) == 0x229;
		st := Swap(st,1);
		//|fp=0x0060|0x24,dst,0x04,src,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x24,dst,0x04,src,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x44,dst,0x04,src,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|dst,0x44,0x04,src,0x229,transferFrom|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x44,dst,src,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x44,0x04,dst,src,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x021a(src,dst,callSig,st);
		return st;
	}

	method block_0_0x021a(src: u160, dst: u160,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x021a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Stack items
	requires st'.evm.stack.contents == [0x44,0x04,dst as u256,src as u256,0x229,callSig]
	requires callSig == 0x23b872dd
	
	requires st'.evm.context.callValue == 0
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x44,0x04,dst,src,0x229,transferFrom|
		st := Dup(st,1);
		//|fp=0x0060|0x44,0x44,0x04,dst,src,0x229,transferFrom|
		st := CallDataLoad(st);
		//|fp=0x0060|wad,0x44,0x04,dst,src,0x229,transferFrom| i.e. address from callData[0x44] == parm2 == wad uint256
		var wad := st.Peek(0);
		assert wad == st.evm.context.CallDataRead(0x44) ;
		st := Swap(st,1);
		//|fp=0x0060|0x44,wad,0x04,dst,src,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x44,wad,0x04,dst,src,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x64,wad,0x04,dst,src,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|wad,0x64,0x04,dst,src,0x229,transferFrom|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x64,wad,dst,src,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x64,0x04,wad,dst,src,0x229,transferFrom|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents[0..6] == [0x64,0x04,wad,dst as u256,src as u256,0x229];
		st := block_0_0x0223(src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0223(src: u160, dst: u160, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0223
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Stack items
	requires st'.evm.stack.contents == [0x64,0x04,wad,dst as u256,src as u256,0x229,callSig]
	requires callSig == 0x23b872dd
	
	requires st'.evm.context.callValue == 0
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x64,0x04,wad,dst,src,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|0x04,wad,dst,src,0x229,transferFrom|
		st := Pop(st);
		//|fp=0x0060|wad,dst,src,0x229,transferFrom|
		st := Push2(st,0x068c);
		//|fp=0x0060|0x68c,wad,dst,src,0x229,transferFrom|
		assume {:axiom} st.IsJumpDest(0x68c);
		st := Jump(st);
		//|fp=0x0060|wad,dst,src,0x229,transferFrom|
		stackLemma(st,st.Operands());
		st := block_0_0x068c(src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0243(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0243
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires callSig == 0x2e1a7d4d
	requires st'.evm.stack.contents == [callSig]

	ensures st'.evm.context.callValue != 0 ==> st''.IsRevert()
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|callSig|
		st := JumpDest(st);
		//|fp=0x0060|callSig|
		st := CallValue(st);
		//|fp=0x0060|callVal,callSig|
		st := IsZero(st);
		//|fp=0x0060|callVal==0,callSig|
		st := Push2(st,0x024e);
		//|fp=0x0060|0x24e,callVal==0,callSig|
		assume {:axiom} st.IsJumpDest(0x24e);
		st := JumpI(st);
		if st.PC() == 0x24e { 
			assert st.evm.context.callValue == 0;
			stackLemma(st,st.Operands());
			st := block_0_0x024e(callSig,st); 
			return st;
		} // i.e. call value is 0
		//|fp=0x0060|callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,callSig|
		st := Revert(st);
		return st;
	}

	method block_0_0x024e(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x024e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires st'.evm.stack.contents == [callSig]
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	{
		// call value is 0
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|callSig|
		st := JumpDest(st);
		//|fp=0x0060|callSig|
		st := Push2(st,0x0264);
		//|fp=0x0060|0x264,callSig|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x04,0x264,callSig|
		st := CallDataLoad(st);
		//|fp=0x0060|data[4],0x04,0x04,0x264,callSig|
		var wad := st.Peek(0);
		assert wad == st.evm.context.CallDataRead(0x4);

		st := Swap(st,1);
		//|fp=0x0060|0x04,wad,0x04,0x264,callSig|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,wad,0x04,0x264,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x025a(wad,callSig,st);
		return st;
	}

	method block_0_0x025a(wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x025a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Stack items
	requires st'.evm.stack.contents == [0x20,0x04,wad,0x04,0x264,callSig]
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	{
		var st := st';
		//|fp=0x0060|0x20,0x04,wad,0x04,0x264,callSig|
		stackLemma(st,st.Operands());
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x24,wad,0x04,0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|wad,0x24,0x04,0x264,callSig|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,wad,0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,wad,0x264,callSig|
		st := Pop(st);
		//|fp=0x0060|0x04,wad,0x264,callSig|
		st := Pop(st);
		//|fp=0x0060|wad,0x264,callSig|
		st := Push2(st,0x09d9);
		//|fp=0x0060|0x9d9,wad,0x264,callSig|
		assume {:axiom} st.IsJumpDest(0x9d9);
		st := Jump(st);
		//|fp=0x0060|wad,0x264,callSig|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents[0..2] == [wad,0x264];
		st := block_0_0x09d9(wad,callSig,st);
		return st;
	}

	method block_0_0x0264(exitCode: u256, bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0264
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires st'.evm.stack.contents == [callSig]
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires exitCode != 0 // i.e.call RETURNS without error
	// Storage
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	
	ensures st''.RETURNS? && st''.data == []
	// TODO: ensures st''.world.Read(st''.context.address,hash) == bal' // st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Stop(st);
		return st;
	}

	method block_0_0x09d9(wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09d9
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Stack items
	requires st'.evm.stack.contents == [wad,0x264,callSig]
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,0x264,callSig|
		st := JumpDest(st);
		//|fp=0x0060|wad,0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|wad,wad,0x264,callSig|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,wad,wad,0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x03,wad,wad,0x264,callSig|
		st := Caller(st);
		//|fp=0x0060|caller,0x00,0x03,wad,wad,0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,wad,wad,0x264,_|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,wad,wad,0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,wad,wad,0x264,callSig|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents[0..7] == [0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff,st.evm.context.sender as u256,0x0,0x03,wad,wad,0x264];
		st := block_0_0x0a0b(wad,callSig,st);
		return st;
	}

	method block_0_0x0a0b(wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a0b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Stack items
	requires st'.evm.stack.contents == [0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff,
												st'.evm.context.sender as u256,0x0,0x03,wad,wad,0x264,callSig]
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,wad,wad,0x264,callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,wad,wad,0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x00,0x03,wad,wad,0x264,callSig|
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0a0e(wad,callSig,st);
		return st;
	}

	method block_0_0x0a0e(wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a0e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 6
	// Stack items
	requires st'.evm.stack.contents == [0x0,0x03,wad,wad,0x264,callSig]
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x00,0x03,wad,wad,0x264,callSig| // st.Read(0x00) == caller
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,wad,wad,0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,wad,wad,0x264,callSig|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents[0..5] == [0x20,0x03,wad,wad,0x264];
		st := block_0_0x0a11(wad,callSig,st);
		return st;
	}

	method block_0_0x0a11(wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a11
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 6
	// Stack items
	requires st'.evm.stack.contents == [0x20,0x03,wad,wad,0x264,callSig]
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	{
		var st := st';	
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x03,wad,wad,0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,wad,0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,wad,0x264,callSig|
		st := MStore(st);
		//|fp=0x0060|0x20,wad,wad,0x264,callSig| // st.Read(0x20) == 0x03
		stackLemma(st,st.Operands());
		st := block_0_0x0a14(wad,callSig,st);
		return st;
	}

	method block_0_0x0a14(wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a14
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 5
	// Stack items
	requires st'.evm.stack.contents == [0x20,wad,wad,0x264,callSig]
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,wad,wad,0x264,callSig|
		st := Push1(st,0x20);
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x20,wad,wad,0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,wad,0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,wad,wad,0x264,callSig|
		st := Keccak256(st);
		HashEquivalenceAxiom(st,st.Peek(0),st.evm.context.sender as u256,0x03);
		assert st.Peek(0) == Hash(st.evm.context.sender as u256,0x03);
		//|fp=0x0060|hash,wad,wad,0x264,callSig|
		//stackLemma(st,st.Operands());
		st := SLoad(st);
		//|fp=0x0060|bal,wad,wad,0x264,callSig|
		var bal := st.Peek(0);
		assert bal == st.Load(Hash(st.evm.context.sender as u256,0x03));
		st := Lt(st);
		//|fp=0x0060|bal<wad,wad,0x264,callSig|
		//assert if bal < wad then st.Peek(0) == 1 else st.Peek(0) == 0 ;
		st := IsZero(st);
		//assert st.Peek(2) == 0x264;    
		//|fp=0x0060|{0,1},wad,0x264,callSig|
		st := IsZero(st);
		//|fp=0x0060|{1,0},wad,0x264,callSig|
		//assert if bal < wad then st.Peek(0) == 1 else st.Peek(0) == 0;
		stackLemma(st,st.Operands());
		//assert if bal < wad then st.evm.stack.contents[0..3] == [1,wad,0x264] else st.evm.stack.contents[0..3] == [0,wad,0x264];
		st := block_0_0x0a1e(bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0a1e(bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a1e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 4
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires if bal < wad then st'.evm.stack.contents == [1,wad,0x264,callSig] else st'.evm.stack.contents == [0,wad,0x264,callSig]
	// Storage
	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))

	ensures bal < wad ==> st''.IsRevert()
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|{1,0},wad,0x264,callSig|
		st := IsZero(st);
		//|fp=0x0060|{0,1},wad,0x264,callSig|
		st := Push2(st,0x0a27);
		//|fp=0x0060|0xa27,{0,1},wad,0x264,callSig|
		assume {:axiom} st.IsJumpDest(0xa27);
		st := JumpI(st);
		if st.PC() == 0xa27 {  // i.e. bal>=wad
			//assert bal >= wad;
			stackLemma(st,st.Operands());
			st := block_0_0x0a27(bal,wad,callSig,st); 
			return st;
		} 
		//|fp=0x0060|wad,0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,wad,0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,wad,0x264,callSig|
		st := Revert(st);
		return st;
	}

	method block_0_0x0a27(bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a27
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 3
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [wad,0x264,callSig]
	// Storage
	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))
	requires bal >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,0x264,callSig|
		st := JumpDest(st);
		//|fp=0x0060|wad,0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|wad,wad,0x264,callSig|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,wad,wad,0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x03,wad,wad,0x264,callSig|
		st := Caller(st);
		//|fp=0x0060|caller,0x00,0x03,wad,wad,0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03wad,wad,0x264,_|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,wad,wad,0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,wad,wad,0x264,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x0a59(bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0a59(bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a59
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 8
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff,st'.evm.context.sender as u256,0x0,0x03,wad,wad,0x264,callSig]
	// Storage
	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))
	requires bal >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,wad,wad,0x264,callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,wad,wad,0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x00,0x03,wad,wad,0x264,callSig|
		//assert st.Peek(0) == 0x00;
		st := MStore(st);
		//|fp=0x0060|0x00,0x03,wad,wad,0x264,callSig| // st.Read(0x00) == caller
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,wad,wad,0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,wad,wad,0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,wad,0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,wad,0x264,callSig|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents[0..6] == [0x20,0x03,0x20,wad,wad,0x264];
		st := block_0_0x0a61(bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0a61(bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a61
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60  && st'.Read(0x00) == st'.evm.context.sender as u256 //&& st'.Read(0x20) == 0x03 
	// Stack height(s)
	requires st'.Operands() == 7
	// Sttack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [0x20,0x03,0x20,wad,wad,0x264,callSig]
	// Storage
	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))
	requires bal >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x03,0x20,wad,wad,0x264,callSig|
		st := MStore(st);
		//|fp=0x0060|0x20,wad,wad,0x264,callSig| // assert st.Read(0x20) == 0x03;
		stackLemma(st,st.Operands());
		st := block_0_0x0a62(bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0a62(bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a62
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256 && st'.Read(0x20) == 0x03 
	// Stack height(s)
	requires st'.Operands() == 5
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [0x20,wad,wad,0x264,callSig]
	// Storage
	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))
	requires bal >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,wad,wad,0x264,callSig| 
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,wad,0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,wad,0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,wad,wad,0x264,callSig|
		st := Keccak256(st);
		HashEquivalenceAxiom(st,st.Peek(0),st.evm.context.sender as u256,0x03);
		assert st.Peek(0) == Hash(st.evm.context.sender as u256,0x03);
		stackLemma(st,st.Operands());
		//|fp=0x0060|hash,wad,wad,0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash,wad,wad,0x264,callSig|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x00,hash,wad,wad,0x264,callSig|
		st := Dup(st,3);
		//|fp=0x0060|hash,wad,0x00,hash,wad,wad,0x264,callSig|
		st := SLoad(st);
		//|fp=0x0060|bal,wad,0x00,hash,wad,wad,0x264,callSig|
		//assert bal == st.Peek(0);
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents[0..7] == [bal,wad,0x0,Hash(st.evm.context.sender as u256,0x03),wad,wad,0x264];
		st := block_0_0x0a6d(bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0a6d(bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a6d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 8
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [bal,wad,0x0,Hash(st'.evm.context.sender as u256,0x03),wad,wad,0x264,callSig]
	requires bal >= wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|bal,wad,0x00,hash,wad,wad,0x264,callSig|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|bal-wad,0x00,hash,wad,wad,0x264,callSig|
		st := Swap(st,3);
		//|fp=0x0060|wad,0x00,hash,bal-wad,wad,0x264,callSig|
		st := Pop(st);
		//|fp=0x0060|0x00,hash,bal-wad,wad,0x264,callSig|
		st := Pop(st);
		//|fp=0x0060|hash,bal-wad,wad,0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|bal-wad,hash,bal-wad,wad,,0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|hash,bal-wad,bal-wad,wad,,0x264,callSig|
		st := SStore(st);
		//|fp=0x0060|bal-wad,wad,0x264,callSig| // bal' == bal-wad
		st := Pop(st);
		//|fp=0x0060|wad,0x264,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x0a75(bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0a75(bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State) 
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a75
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [wad,0x264,callSig]
	// Storage
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,0x264,callSig|
		st := Caller(st);
		//|fp=0x0060|caller,wad,0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,wad,0x264,callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,wad,0x264,callSig|
		st := Push2(st,0x08fc);
		//|fp=0x0060|0x8fc,caller,wad,0x264,callSig|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x8fc,caller,wad,0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x8fc,wad,caller,wad,0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x8fc,wad,caller,wad,0x264,callSig|
		st := IsZero(st);
		//|fp=0x0060|wad==0,0x8fc,wad,caller,wad,0x264,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x0a93(bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0a93(bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a93
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [0,0x8fc,st'.Peek(2),st'.evm.context.sender as u256,st'.Peek(4),0x264,callSig]
		|| st'.evm.stack.contents == [1,0x8fc,st'.Peek(2),st'.evm.context.sender as u256,st'.Peek(4),0x264,callSig]
	// Storage
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad==0,0x8fc,data[4],caller,data[4],0x264,callSig|
		assert (st.Peek(0) * st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Mul(st);
		//|fp=0x0060|{0,0x8fc},data[4],caller,data[4],0x264,callSig| i.e wad != 0 ==> st.Peek(0) == 0 , wad == 0 ==> st.Peek(0) == 0x8fc
		st := Swap(st,1);
		//|fp=0x0060|data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := MLoad(st);
		//|fp=0x0060|fmp==0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x00,0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x00,0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x00,0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		stackLemma(st,st.Operands());
		st := block_0_0x0a9e(bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0a9e(bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a9e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [0x60,st'.Peek(1),0x0,0x60,st'.Peek(4),0x8fc,st'.Peek(6),st'.Peek(7),0x264,callSig]
		|| st'.evm.stack.contents == [0x60,st'.Peek(1),0x0,0x60,st'.Peek(4),0,st'.Peek(6),st'.Peek(7),0x264,callSig]
	// Storage
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x60,0x00,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		st := Dup(st,4);
		//|fp=0x0060|0x60,0x60,0x60,0x00,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x60,0x60,0x60,0x00,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		st := Sub(st);
		//|fp=0x0060|0x00,0x60,0x00,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,0x00,0x60,0x00,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		st := Dup(st,6);
		//|fp=0x0060|wad,0x60,0x00,0x60,0x00,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		st := Dup(st,9);
		//|fp=0x0060|caller,wad,0x60,0x00,0x60,0x00,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		st := Dup(st,9);
		//|fp=0x0060|{0,0x8fc},caller,wad,0x60,0x00,0x60,0x00,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		stackLemma(st,st.Operands());
		var temp := st;
		var CONTINUING(cc) := Call(st);
		{
			var inner := cc.CallEnter(1);
			if inner.EXECUTING? { inner := external_call(cc.sender,inner); }
			st := cc.CallReturn(inner);
		}
		//|fp=0x0060|exitcode,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		var exitCode := st.Peek(0);
		MemoryPreserved(st,temp); 
		//assume st.Read(0x40) == 0x60;
		StoragePreserved(st,temp,Hash(st.evm.context.sender as u256,0x03)); 
		//assume st.Load(Hash(st.evm.context.sender as u256,0x03)) == bal - wad; 

		st := Swap(st,4);
		//|fp=0x0060|caller,0x60,wad,{0,0x8fc},exitCode,wad,0x264,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0aa6(exitCode,bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0aa6(exitCode: u256, bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0aa6
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [st'.Peek(0),st'.Peek(1),st'.Peek(2),st'.Peek(3),exitCode,st'.Peek(5),0x264,callSig]
	// Storage
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|caller,0x60,wad,{0,0x8fc},exitCode,wad,0x264,_|
		st := Pop(st);
		//|fp=0x0060|0x60,wad,{0,0x8fc},exitCode,wad,0x264,_|
		st := Pop(st);
		//|fp=0x0060|wad,{0,0x8fc},exitCode,wad,0x264,_|
		st := Pop(st);
		//|fp=0x0060|{0,0x8fc},exitCode,wad,0x264,_|
		st := Pop(st);
		//|fp=0x0060|exitCode,wad,0x264,_|
		st := IsZero(st);
		//|fp=0x0060|{exitCode==0},wad,0x264,_|
		st := IsZero(st);
		//|fp=0x0060|{exitCode!=0},wad,0x264,_|
		st := Push2(st,0x0ab4);
		//|fp=0x0060|0xab4,{exitCode!=0},wad,0x264,_|
		assume {:axiom} st.IsJumpDest(0xab4);
		st := JumpI(st);
		if st.PC() == 0xab4 {  // i.e. exitCode!=0, call RETURNS without error
			//|fp=0x0060|wad,0x264,_|
			stackLemma(st,st.Operands());
			st := block_0_0x0ab4(exitCode,bal,wad,callSig,st); 
			return st;
		}
		stackLemma(st,st.Operands());
		st := block_0_0x0ab0(exitCode,callSig,st); // i.e. revert
		return st;
	}

	method block_0_0x0ab0(exitCode: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ab0
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires exitCode == 0 // i.e.call RETURNS with error
	
	ensures st''.IsRevert() && st''.data == [] // Memory.Slice(st'.evm.memory, 0x00, 0x00)
	
	{
		var st := st';
		//|fp=0x0060|wad,0x264,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,wad,0x264,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,wad,0x264,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x0ab4(exitCode: u256, bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ab4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [st'.Peek(0),0x264,callSig]
	requires exitCode != 0 // i.e.call RETURNS without error
	// Storage 
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,0x264,_|
		st := JumpDest(st);
		//|fp=0x0060|wad,0x264,_|
		st := Caller(st);
		//|fp=0x0060|caller,wad,0x264,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,wad,0x264,_|
		st := AndU160(st);
		//|fp=0x0060|caller,wad,0x264,_|
		st := PushN(st,32,0x7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65);
		//|fp=0x0060|0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		stackLemma(st,st.Operands());
		st := block_0_0x0af1(exitCode, bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0af1(exitCode: u256, bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0af1
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0x264,callSig]
	requires exitCode != 0 // i.e.call RETURNS without error
	// Storage
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x60,0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,wad,0x60,0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_0_0x0af5(exitCode, bal,wad,callSig,st);
		return st;
	}
		
	method block_0_0x0af5(exitCode: u256, bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0af5
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),st'.Peek(5),0x264,callSig]
	requires exitCode != 0 // i.e.call RETURNS without error
	// Storage
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Swap(st,2);
		//|fp=0x0060|wad,0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents[0..6] == [st.Peek(0),0x80,st.Peek(2),st.Peek(3),st.Peek(4),0x264];
		st := block_0_0x0afa(exitCode, bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0afa(exitCode: u256, bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0afa
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [st'.Peek(0),0x80,st'.Peek(2),st'.Peek(3),st'.Peek(4),0x264,callSig]
	requires exitCode != 0 // i.e.call RETURNS without error
	// Storage
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Pop(st);
		//|fp=0x0060|0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		assert st.Peek(1) <= st.Peek(0);
		stackLemma(st,st.Operands());
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := LogN(st,2);
		//|fp=0x0060|wad,0x264,_| i.e. append to log (0x60,0x20,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller)
		stackLemma(st,st.Operands());
		st := block_0_0x0b03(exitCode,bal,wad,callSig,st);
		return st;
	}

	method block_0_0x0b03(exitCode: u256, bal: u256, wad: u256,  callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b03
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires callSig == 0x2e1a7d4d && st'.evm.context.callValue == 0 
	requires st'.evm.stack.contents == [st'.Peek(0),0x264,callSig]
	requires exitCode != 0 // i.e.call RETURNS without error
	// Storage
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		//|fp=0x0060|wad,0x264,_|
		st := Pop(st);
		//|fp=0x0060|0x264,_|
		assume {:axiom} st.IsJumpDest(0x264);
		st := Jump(st);
		st := block_0_0x0264(exitCode,bal,wad,callSig,st);
		return st;
	}

}
