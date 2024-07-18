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

	method block_0_0x0000(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0000
	// Stack height(s)
	requires st'.Operands() == 0
	// Storage
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.
  	requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.
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
		if st.PC() == 0xaf {st := block_0_0x00af(st); return st;} // call data size < 0x04
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
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.
  	requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.
	{
		// implies calll data size >=  4 bytes
		var st := st';
		//|fp=0x0060||
		st := Push1(st,0x00);
		//|fp=0x0060|0x00|
		st := CallDataLoad(st);
		//|fp=0x0060|data[0]|
		st := PushN(st,29,0x0100000000000000000000000000000000000000000000000000000000);
		//|fp=0x0060|0x100000000000000,data[0]|
		st := Swap(st,1);
		//|fp=0x0060|data[0],0x100000000000000|
		st := Div(st);
		//|fp=0x0060|_|
		st := Push4(st,0xffffffff);
		//|fp=0x0060|0xffffffff,_|
		st := AndU32(st);
		//|fp=0x0060|call sig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig| // first 4 bytes of call data
		st := block_0_0x0037(st);
		return st;
	}

	method block_0_0x0037(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0037
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Storage
	requires st'.Load(0) == 13 * 2 // length of "Wrapped Ether", shifted left.
  	requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.
	{
		var st := st';
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x06fdde03);
		//|fp=0x0060|0x6fdde03,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x6fdde03==callSig,callSig|
		st := Push2(st,0x00b9);
		//|fp=0x0060|0xb9,0x6fdde03==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0xb9);
		st := JumpI(st);
		if st.PC() == 0xb9 { st := block_0_0x00b9(st); return st;} // fn 0x6fdde03 i.e. name
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x095ea7b3);
		//|fp=0x0060|0x95ea7b3,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x95ea7b3==callSig,callSig|
		st := Push2(st,0x0147);
		//|fp=0x0060|0x0147,0x95ea7b3==callSig,callSig|
		st := block_0_0x004b(st);
		return st;
	}

	method block_0_0x004b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x004b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == 0x147)
	// Termination
  	requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.
	{
		var st := st';
		//|fp=0x0060|0x0147,0x95ea7b3==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x147);
		st := JumpI(st);
		if st.PC() == 0x147 { st := block_0_0x0147(st); return st;} // fn 0x95ea7b3 i.e. approve
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
		if st.PC() == 0x1a1 { st := block_0_0x01a1(st); return st;} // fn 0x18160ddd i.e. total supply
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x23b872dd);
		//|fp=0x0060|0x23b872dd,callSig,callSig|
		st := block_0_0x005d(st);
		return st;
	}

	method block_0_0x005d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x005d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Termination
  	requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.
	{
		var st := st';
		//|fp=0x0060|0x23b872dd,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x23b872dd==callSig,callSig|
		st := Push2(st,0x01ca);
		//|fp=0x0060|0x1ca,0x23b872dd==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x1ca);
		st := JumpI(st);
		if st.PC() == 0x1ca { st := block_0_0x01ca(st); return st;} // fn 0x23b872dd i.e. ????
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
		if st.PC() == 0x243 { st := block_0_0x0243(st); return st;} // fn 0x2e1a7d4d ie. ????
		//|fp=0x0060|callSig|
		st := block_0_0x006d(st);
		return st;
	}

	method block_0_0x006d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x006d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	// Termination
  	requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.
	{
		var st := st';
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
		if st.PC() == 0x266 { st := block_0_0x0266(st); return st;} // fn 0x313ce567 i.e. decimals
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0x70a08231);
		//|fp=0x0060|0x70a08231,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0x70a08231==callSig,callSig|
		st := block_0_0x007f(st);
		return st;
	}

	method block_0_0x007f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x007f
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Termination
  	requires st'.Load(0x01) == 4 * 2 // length of "WETH", shifted left.
	{
		var st := st';
		//|fp=0x0060|0x70a08231==callSig,callSig|
		st := Push2(st,0x0295);
		//|fp=0x0060|0x295,0x70a08231==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x295);
		st := JumpI(st);
		if st.PC() == 0x295 { st := block_0_0x0295(st); return st;} // fn 0x70a08231 ie. ???
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
		if st.PC() == 0x2e2 { st := block_0_0x02e2(st); return st;} // fn 0x95d89b41 i.e. symbol
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := block_0_0x008f(st);
		return st;
	}

	method block_0_0x008f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x008f
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	{
		var st := st';
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0xa9059cbb);
		//|fp=0x0060|0xa9059cbb,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0xa9059cbb==callSig,callSig|
		st := Push2(st,0x0370);
		//|fp=0x0060|0x370,0xa9059cbb==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x370);
		st := JumpI(st);
		if st.PC() == 0x370 { st := block_0_0x0370(st); return st;} //i.e. fn 0xa9059cbb
		//|fp=0x0060|callSig|
		st := Dup(st,1);
		//|fp=0x0060|callSig,callSig|
		st := Push4(st,0xd0e30db0);
		//|fp=0x0060|0xd0e30db0,callSig,callSig|
		st := Eq(st);
		//|fp=0x0060|0xd0e30db0==callSig,callSig|
		st := Push2(st,0x03ca);
		//|fp=0x0060|0x03ca,0xd0e30db0==callSig,callSig|
		st := block_0_0x00a3(st);
		return st;
	}

	method block_0_0x00a3(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00a3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == 0x3ca)
	{
		var st := st';
		//|fp=0x0060|0x03ca,0xd0e30db0==callSig,callSig|
		assume {:axiom} st.IsJumpDest(0x3ca);
		st := JumpI(st);
		if st.PC() == 0x3ca { st := block_0_0x03ca(st); return st;}
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
		if st.PC() == 0x3d4 { st := block_0_0x03d4(st); return st;} // fn 0xdd62ed3e
		//|fp=0x0060|callSig|
		st := block_0_0x00af(st);
		return st;
	}

	method block_0_0x00af(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x00af
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() >= 0 && st'.Operands() <= 1
	{
		var st := st';
		// from a3: |fp=0x0060|callSig|
		//|fp=0x0060||
		st := JumpDest(st);
		// from a3: |fp=0x0060|callSig|
		//|fp=0x0060|_|
		//|fp=0x0060||
		st := Push2(st,0x00b7);
		// from a3: |fp=0x0060|0x00b7,callSig|
		//|fp=0x0060|0xb7,_|
		//|fp=0x0060|0xb7|
		st := Push2(st,0x0440);
		// from a3: |fp=0x0060|0x0440,0x00b7,callSig|
		//|fp=0x0060|0x440,0xb7,_|
		//|fp=0x0060|0x440,0xb7|
		assume {:axiom} st.IsJumpDest(0x440);
		st := Jump(st);
		// from a3: |fp=0x0060|0x00b7,callSig|
		st := block_0_0x0440(st);
		return st;
	}

	method block_0_0x01ca(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01ca
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|callSig|
		st := JumpDest(st);
		//|fp=0x0060|callSig|
		st := CallValue(st);
		//|fp=0x0060|callVal,callSig|
		st := IsZero(st);
		//|fp=0x0060|callVal==0,callSig|
		st := Push2(st,0x01d5);
		//|fp=0x0060|0x1d5,callVal==0,callSig|
		assume {:axiom} st.IsJumpDest(0x1d5);
		st := JumpI(st);
		if st.PC() == 0x1d5 { st := block_0_0x01d5(st); return st;} // call value is zero
		//|fp=0x0060|callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,callSig|
		st := Revert(st);
		return st;
	}

	method block_0_0x01d5(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01d5
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1

	requires st'.evm.context.callValue == 0
	{
		var st := st';
		//|fp=0x0060|callSig|
		st := JumpDest(st);
		//|fp=0x0060|callSig|
		st := Push2(st,0x0229);
		//|fp=0x0060|0x229,callSig|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,0x229,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x229,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x04,0x229,callSig|
		st := CallDataLoad(st);
		//|fp=0x0060|callData[4],0x04,0x04,0x229,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,callData[4],0x04,0x04,0x229,callSig|
		st := AndU160(st);
		//|fp=0x0060|addr,0x04,0x04,0x229,callSig|  i.e. masking 20 bytes is usually an address
		st := block_0_0x01f4(st);
		return st;
	}

	method block_0_0x01f4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01f4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(1) == 0x4 && st'.Peek(3) == 0x229)
	{
		var st := st';
		//|fp=0x0060|addr,0x04,0x04,0x229,callSig|  i.e. address from call data[4]
		st := Swap(st,1);
		//|fp=0x0060|0x04,addr,0x04,0x229,callSig|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,addr,0x04,0x229,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x24,addr,0x04,0x229,callSig|
		st := Swap(st,1);
		//|fp=0x0060|addr,0x24,0x04,0x229,callSig|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,addr,0x229,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,addr,0x229,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x24,0x24,0x04,addr,0x229,callSig|
		st := CallDataLoad(st);
		//|fp=0x0060|data[0x24],0x24,0x04,addr,0x229,callSig|
		st := block_0_0x01fd(st);
		return st;
	}

	method block_0_0x01fd(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01fd
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(1) == 0x24 && st'.Peek(4) == 0x229)
	{
		var st := st';
		//|fp=0x0060|data[0x24],0x24,0x04,addr,0x229,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,|data[0x24],0x24,0x04,addr,0x229,callSig|
		st := AndU160(st);
		//|fp=0x0060|addr2,0x24,0x04,addr,0x229,callSig| i.e. address from data[0x24]
		st := Swap(st,1);
		//|fp=0x0060|0x24,addr2,0x04,addr,0x229,callSig|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x24,addr2,0x04,addr,0x229,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		assert st.Peek(5) == 0x229;
		st := Add(st);
		//|fp=0x0060|0x44,addr2,0x04,addr,0x229,callSig|
		st := Swap(st,1);
		//|fp=0x0060|addr2,0x44,0x04,addr,0x229,callSig|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x44,addr2,addr,0x229,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x44,0x04,addr2,addr,0x229,callSig|
		st := block_0_0x021a(st);
		return st;
	}

	method block_0_0x021a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x021a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x44 && st'.Peek(4) == 0x229)
	{
		var st := st';
		//|fp=0x0060|0x44,0x04,addr2,addr,0x229,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x44,0x44,0x04,addr2,addr,0x229,callSig|
		st := CallDataLoad(st);
		//|fp=0x0060|data[0x44],0x44,0x04,addr2,addr,0x229,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x44,data[0x44],0x04,addr2,addr,0x229,callSig|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x44,data[0x44],0x04,addr2,addr,0x229,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x64,data[0x44],0x04,addr2,addr,0x229,callSig|
		st := Swap(st,1);
		//|fp=0x0060|data[0x44],0x64,0x04,addr2,addr,0x229,callSig|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x64,data[0x44],addr2,addr,0x229,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x64,0x04,data[0x44],addr2,addr,0x229,callSig|
		st := block_0_0x0223(st);
		return st;
	}

	method block_0_0x0223(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0223
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(5) == 0x229)
	{
		var st := st';
		//|fp=0x0060|0x64,0x04,data[0x44],addr2,addr,0x229,callSig|
		st := Pop(st);
		//|fp=0x0060|0x04,data[0x44],addr2,addr,0x229,callSig|
		st := Pop(st);
		//|fp=0x0060|data[0x44],addr2,addr,0x229,callSig|
		st := Push2(st,0x068c);
		//|fp=0x0060|0x68c,data[0x44],addr2,addr,0x229,callSig|
		assume {:axiom} st.IsJumpDest(0x68c);
		st := Jump(st);
		//|fp=0x0060|data[0x44],addr2,addr,0x229,callSig|
		st := block_0_0x068c(st);
		return st;
	}

	method block_0_0x0243(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0243
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
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
		if st.PC() == 0x24e { st := block_0_0x024e(st); return st;} // i.e. call value is 0
		//|fp=0x0060|callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,callSig|
		st := Revert(st);
		return st;
	}

	method block_0_0x024e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x024e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		// call value is 0
		var st := st';
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
		st := Swap(st,1);
		//|fp=0x0060|0x04,data[4],0x04,0x264,callSig|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,data[4],0x04,0x264,callSig|
		st := block_0_0x025a(st);
		return st;
	}

	method block_0_0x025a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x025a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x4 && st'.Peek(4) == 0x264)
	{
		var st := st';
		//|fp=0x0060|0x20,0x04,data[4],0x04,0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x24,data[4],0x04,0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|data[4],0x24,0x04,0x264,callSig|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,data[4],0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,data[4],0x264,callSig|
		st := Pop(st);
		//|fp=0x0060|0x04,data[4],0x264,callSig|
		st := Pop(st);
		//|fp=0x0060|data[4],0x264,callSig|
		st := Push2(st,0x09d9);
		//|fp=0x0060|0x9d9,data[4],0x264,callSig|
		assume {:axiom} st.IsJumpDest(0x9d9);
		st := Jump(st);
		//|fp=0x0060|data[4],0x264,callSig|
		st := block_0_0x09d9(st);
		return st;
	}

	method block_0_0x0264(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0264
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Stop(st);
		return st;
	}

	method block_0_0x09d9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09d9
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x264)
	{
		var st := st';
		//|fp=0x0060|data[4],0x264,callSig|
		st := JumpDest(st);
		//|fp=0x0060|data[4],0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|data[4],data[4],0x264,callSig|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,data[4],data[4],0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x03,data[4],data[4],0x264,callSig|
		st := Caller(st);
		//|fp=0x0060|caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,_,0x264,_|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := block_0_0x0a0b(st);
		return st;
	}

	method block_0_0x0a0b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a0b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff && st'.Peek(2) == 0x0 
			&& st'.Peek(3) == 0x03 && st'.Peek(4) == st'.Peek(5) && st'.Peek(6) == 0x264)
	{
		var st := st';
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := MStore(st);
		assert {:split_here} true;
		assert (st.Peek(0) == 0x0 && st.Peek(1) == 0x03 && st.Peek(2) == st.Peek(3) && st.Peek(4) == 0x264);
		//|fp=0x0060|0x00,0x03,data[4],data[4],0x264,callSig| // st.Read(0x00) == caller
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,data[4],data[4],0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//assert {:split_here} true;
		//|fp=0x0060|0x20,0x03,data[4],data[4],0x264,callSig|
		assert (st.Peek(0) == 0x20 && st.Peek(1) == 0x03 && st.Peek(2) == st.Peek(3) && st.Peek(4) == 0x264);
		st := block_0_0x0a11(st);
		return st;
	}

	method block_0_0x0a11(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a11
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x03 && st'.Peek(2) == st'.Peek(3) && st'.Peek(4) == 0x264)
	{
		var st := st';	
		//|fp=0x0060|0x20,0x03,data[4],data[4],0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,data[4],data[4],0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,data[4],data[4],0x264,callSig|
		st := MStore(st);
		//|fp=0x0060|0x20,data[4],data[4],0x264,callSig| // st.Read(0x20) == 0x03
		assert st.Read(0x20) == 0x03;
		assert (st.Peek(0) == 0x20 && st.Peek(1) == st.Peek(2) && st.Peek(3) == 0x264);
		st := block_0_0x0a14(st);
		return st;
	}

	method block_0_0x0a14(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a14
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == st'.Peek(2) && st'.Peek(3) == 0x264)
	{
		var st := st';
		//|fp=0x0060|0x20,data[4],data[4],0x264,callSig|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,data[4],data[4],0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,data[4],data[4],0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,data[4],data[4],0x264,callSig|
		st := Keccak256(st);
		var bytes:= Memory.Slice(st.evm.memory,0x00,0x40); 
		var hash := st.evm.precompiled.Sha3(bytes);
		assert st.Peek(0) == hash;
		assert st.Peek(3) == 0x264;    
		//|fp=0x0060|hash,data[4],data[4],0x264,callSig|
		st := SLoad(st);
		//|fp=0x0060|Load(hash),data[4],data[4],0x264,callSig|
		assert st.Peek(0) == st.Load(hash);
		assert st.Peek(1) == st.Peek(2);
		st := Lt(st);
		//|fp=0x0060|Load(hash)<data[4],data[4],0x264,callSig|
		assert if st.Load(hash) < st.Peek(1) then st.Peek(0) == 1 else st.Peek(0) == 0 ;
		st := IsZero(st);
		assert st.Peek(2) == 0x264;    
		//|fp=0x0060|{0,1},data[4],0x264,callSig|
		st := IsZero(st);
		//|fp=0x0060|{1,0},data[4],0x264,callSig|
		assert if st.Load(hash) < st.Peek(1) then st.Peek(0) == 1 else st.Peek(0) == 0;
		//assert st.Peek(2) == 0x264;
		st := block_0_0x0a1e(st);
		return st;
	}

	method block_0_0x0a1e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a1e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x264)

	requires 	var bytes:= Memory.Slice(st'.evm.memory,0x00,0x40); 
				var hash := st'.evm.precompiled.Sha3(bytes);
				if st'.Load(hash) < st'.Peek(1) then st'.Peek(0) == 1 else st'.Peek(0) == 0
	{
		var st := st';
		//|fp=0x0060|{1,0},data[4],0x264,callSig|
		st := IsZero(st);
		//|fp=0x0060|{0,1},data[4],0x264,callSig|
		st := Push2(st,0x0a27);
		//|fp=0x0060|0xa27,{0,1},data[4],0x264,callSig|
		assume {:axiom} st.IsJumpDest(0xa27);
		st := JumpI(st);
		if st.PC() == 0xa27 {  // i.e. Load(hash)>=data[4]
			var bytes:= Memory.Slice(st'.evm.memory,0x00,0x40); 
			var hash := st'.evm.precompiled.Sha3(bytes);
			assert st.Peek(0) == st'.Peek(1);
			assert st.Load(hash) >= st'.Peek(1);
			st := block_0_0x0a27(st); 
			return st;
		} 
		//|fp=0x0060|data[4],0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00data[4],0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,data[4],0x264,callSig|
		st := Revert(st);
		return st;
	}

	method block_0_0x0a27(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a27
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x264)
	requires 	var bytes:= Memory.Slice(st'.evm.memory,0x00,0x40); 
				var hash := st'.evm.precompiled.Sha3(bytes);
				st'.Load(hash) >= st'.Peek(0) 
	{
		var st := st';
		//|fp=0x0060|data[4],0x264,callSig|
		st := JumpDest(st);
		//|fp=0x0060|data[4],0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|data[4],data[4],0x264,callSig|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,data[4],data[4],0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x03,data[4],data[4],0x264,callSig|
		st := Caller(st);
		//|fp=0x0060|caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x00,0x03,_,_,0x264,_|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := block_0_0x0a59(st);
		return st;
	}

	method block_0_0x0a59(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a59
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x03 && st'.Peek(6) == 0x264)
	requires 	var bytes:= Memory.Slice(st'.evm.memory,0x00,0x40); 
				var hash := st'.evm.precompiled.Sha3(bytes);
				st'.Load(hash) >= st'.Peek(4) 
	{
		var st := st';
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x00,0x03,data[4],data[4],0x264,callSig|
		st := MStore(st);
		assert {:split_here} true;
		assert (st.Peek(0) == 0x00 && st.Peek(1) == 0x03 && st.Peek(4) == 0x264);
		//|fp=0x0060|0x00,0x03,data[4],data[4],0x264,callSig| // st.Read(0x00) == caller
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,data[4],data[4],0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		assert {:split_here} true;
		assert (st.Peek(0) == 0x20 && st.Peek(1) == 0x03 && st.Peek(4) == 0x264);
		//|fp=0x0060|0x20,0x03,data[4],data[4],0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,data[4],data[4],0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,data[4],data[4],0x264,callSig|
		assert (st.Peek(0) == 0x20 && st.Peek(1) == 0x03 && st.Peek(2) == 0x20 && st.Peek(5) == 0x264);
		assume Memory.Slice(st'.evm.memory,0x00,0x40) == Memory.Slice(st.evm.memory,0x00,0x40);
		st := block_0_0x0a61(st);
		return st;
	}

	method block_0_0x0a61(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a61
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60  && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x03 && st'.Peek(2) == 0x20 && st'.Peek(5) == 0x264)
	requires 	var bytes:= Memory.Slice(st'.evm.memory,0x00,0x40); 
				var hash := st'.evm.precompiled.Sha3(bytes);
				st'.Load(hash) >= st'.Peek(3) 
	{
		var st := st';
		//|fp=0x0060|0x20,0x03,0x20,data[4],data[4],0x264,callSig|
		st := MStore(st);
		//|fp=0x0060|0x20,data[4],data[4],0x264,callSig| // st.Read(0x20) == 0x03
		assert st.Read(0x00) == st'.Read(0x00) && st.Read(0x20) == 0x03;
		assert st.Peek(1) == st'.Peek(3) ;
		assume Memory.Slice(st'.evm.memory,0x00,0x40) == Memory.Slice(st.evm.memory,0x00,0x40);
		st := block_0_0x0a62(st);
		return st;
	}

	method block_0_0x0a62(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a62
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(3) == 0x264)
	requires 	var bytes:= Memory.Slice(st'.evm.memory,0x00,0x40); 
				var hash := st'.evm.precompiled.Sha3(bytes);
				st'.Load(hash) >= st'.Peek(1)
	{
		var st := st';
		//|fp=0x0060|0x20,data[4],data[4],0x264,callSig| 
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,data[4],data[4],0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,data[4],data[4],0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,data[4],data[4],0x264,callSig|
		st := Keccak256(st);
		//|fp=0x0060|hash,data[4],data[4],0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash,data[4],data[4],0x264,callSig|
		st := Dup(st,3);
		//|fp=0x0060|data[4],0x00,hash,data[4],data[4],0x264,callSig|
		st := Dup(st,3);
		//|fp=0x0060|hash,data[4],0x00,hash,data[4],data[4],0x264,callSig|
		st := SLoad(st);
		//|fp=0x0060|Load(hash),data[4],0x00,hash,data[4],data[4],0x264,callSig|
		st := block_0_0x0a6d(st);
		return st;
	}

	method block_0_0x0a6d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a6d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(6) == 0x264)
	requires 	var bytes:= Memory.Slice(st'.evm.memory,0x00,0x40); 
				var hash := st'.evm.precompiled.Sha3(bytes);
				st'.Peek(0) >= st'.Peek(1)
	{
		var st := st';
		//|fp=0x0060|Load(hash),data[4],0x00,hash,data[4],data[4],0x264,callSig|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|Load(hash)-data[4],0x00,hash,data[4],data[4],0x264,callSig|
		st := Swap(st,3);
		//|fp=0x0060|data[4],0x00,hash,Load(hash)-data[4],data[4],0x264,callSig|
		st := Pop(st);
		//|fp=0x0060|0x00,hash,Load(hash)-data[4],data[4],0x264,callSig|
		st := Pop(st);
		//|fp=0x0060|hash,Load(hash)-data[4],data[4],0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|Load(hash)-data[4],hash,Load(hash)-data[4],data[4],0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|hash,Load(hash)-data[4],Load(hash)-data[4],data[4],0x264,callSig|
		st := SStore(st);
		//|fp=0x0060|Load(hash)-data[4],data[4],0x264,callSig| // Load(hash) == Load(hash)-data[4]
		st := Pop(st);
		//|fp=0x0060|data[4],0x264,callSig|
		st := block_0_0x0a75(st);
		return st;
	}

	method block_0_0x0a75(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a75
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x264)
	{
		var st := st';
		//|fp=0x0060|data[4],0x264,callSig|
		st := Caller(st);
		//|fp=0x0060|caller,data[4],0x264,callSig|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,data[4],0x264,callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,data[4],0x264,callSig|
		st := Push2(st,0x08fc);
		//|fp=0x0060|0x8fc,caller,data[4],0x264,callSig|
		st := Dup(st,3);
		//|fp=0x0060|data[4],0x8fc,caller,data[4],0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x8fc,data[4],caller,data[4],0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|data[4],0x8fc,data[4],caller,data[4],0x264,callSig|
		st := IsZero(st);
		//|fp=0x0060|data[4]==0,0x8fc,data[4],caller,data[4],0x264,callSig|
		st := block_0_0x0a93(st);
		return st;
	}

	method block_0_0x0a93(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a93
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires ((st'.Peek(0) == 0 || st'.Peek(0) == 1) && st'.Peek(1) == 0x8fc && st'.Peek(5) == 0x264)
	{
		var st := st';
		//|fp=0x0060|data[4]==0,0x8fc,data[4],caller,data[4],0x264,callSig|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		//|fp=0x0060|{0,0x8fc},data[4],caller,data[4],0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := MLoad(st);
		//|fp=0x0060|0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x00,0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x00,0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x00,0x60,data[4],{0,0x8fc},caller,data[4],0x264,callSig|
		st := block_0_0x0a9e(st);
		return st;
	}

	method block_0_0x0a9e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a9e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(3) == 0x60 && st'.Peek(8) == 0x264)
	{
		var st := st';
		//|fp=0x0060|0x60,0x60,0x00,0x60,_,_,_,_,0x264,_|
		st := Dup(st,4);
		//|fp=0x0060|0x60,0x60,0x60,0x00,0x60,_,_,_,_,0x264,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x60,0x60,0x60,0x00,0x60,_,_,_,_,0x264,_|
		st := Sub(st);
		//|fp=0x0060|0x00,0x60,0x00,0x60,_,_,_,_,0x264,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,0x00,0x60,0x00,0x60,_,_,_,_,0x264,_|
		st := Dup(st,6);
		//|fp=0x0060|_,0x60,0x00,0x60,0x00,0x60,_,_,_,_,0x264,_|
		st := Dup(st,9);
		//|fp=0x0060|_,_,0x60,0x00,0x60,0x00,0x60,_,_,_,_,0x264,_|
		st := Dup(st,9);
		//|fp=0x0060|_,_,_,0x60,0x00,0x60,0x00,0x60,_,_,_,_,0x264,_|
		var CONTINUING(cc) := Call(st);
		{
			var inner := cc.CallEnter(1);
			if inner.EXECUTING? { inner := external_call(cc.sender,inner); }
			st := cc.CallReturn(inner);
		}
		//|fp=0x0060|_,0x60,_,_,_,_,0x264,_|
		st := Swap(st,4);
		assume st.Read(0x40) == 0x60; 
		st := block_0_0x0aa6(st);
		return st;
	}

	method block_0_0x0aa6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0aa6
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(6) == 0x264)
	{
		var st := st';
		//|fp=0x0060|_,0x60,_,_,_,_,0x264,_|
		st := Pop(st);
		//|fp=0x0060|0x60,_,_,_,_,0x264,_|
		st := Pop(st);
		//|fp=0x0060|_,_,_,_,0x264,_|
		st := Pop(st);
		//|fp=0x0060|_,_,_,0x264,_|
		st := Pop(st);
		//|fp=0x0060|_,_,0x264,_|
		st := IsZero(st);
		//|fp=0x0060|_,_,0x264,_|
		st := IsZero(st);
		//|fp=0x0060|_,_,0x264,_|
		st := Push2(st,0x0ab4);
		//|fp=0x0060|0xab4,_,_,0x264,_|
		assume {:axiom} st.IsJumpDest(0xab4);
		st := JumpI(st);
		if st.PC() == 0xab4 { st := block_0_0x0ab4(st); return st;}
		st := block_0_0x0ab0(st);
		return st;
	}

	method block_0_0x0ab0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ab0
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	{
		var st := st';
		//|fp=0x0060|_,0x264,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_,0x264,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_,0x264,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x0ab4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ab4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x264)
	{
		var st := st';
		//|fp=0x0060|_,0x264,_|
		st := JumpDest(st);
		//|fp=0x0060|_,0x264,_|
		st := Caller(st);
		//|fp=0x0060|_,_,0x264,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,_,0x264,_|
		st := AndU160(st);
		//|fp=0x0060|_,_,0x264,_|
		st := PushN(st,32,0x7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65);
		//|fp=0x0060|0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Dup(st,3);
		//|fp=0x0060|_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := MLoad(st);
		st := block_0_0x0af1(st);
		return st;
	}

	method block_0_0x0af1(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0af1
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(5) == 0x264)
	{
		var st := st';
		//|fp=0x0060|0x60,_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Dup(st,3);
		//|fp=0x0060|_,0x60,0x60,_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,_,0x60,0x60,_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		//|fp=0x0060|0x20,0x60,0x60,_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Add(st);
		//|fp=0x0060|0x80,0x60,_,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Swap(st,2);
		//|fp=0x0060|_,0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Pop(st);
		st := block_0_0x0afa(st);
		return st;
	}

	method block_0_0x0afa(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0afa
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(1) == 0x80 && st'.Peek(5) == 0x264)
	{
		var st := st';
		//|fp=0x0060|0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Pop(st);
		//|fp=0x0060|0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,_,_,0x264,_|
		st := LogN(st,2);
		st := block_0_0x0b03(st);
		return st;
	}

	method block_0_0x0b03(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b03
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x264)
	{
		var st := st';
		//|fp=0x0060|_,0x264,_|
		st := Pop(st);
		//|fp=0x0060|0x264,_|
		assume {:axiom} st.IsJumpDest(0x264);
		st := Jump(st);
		st := block_0_0x0264(st);
		return st;
	}

}
