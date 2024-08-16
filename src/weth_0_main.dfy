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
		//|fp=0x0060|cData[0x00]|
		st := PushN(st,29,0x0100000000000000000000000000000000000000000000000000000000);
		//|fp=0x0060|0x100000000000000,cData[0x00]|
		st := Swap(st,1);
		//|fp=0x0060|cData[0x00],0x100000000000000|
		st := Bytecode.Div(st);
		//|fp=0x0060|_|
		st := Push4(st,0xffffffff);
		//|fp=0x0060|0xffffffff,_|
		st := AndU32(st);
		//|fp=0x0060|callSig|
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
		if st.PC() == 0xb9 { st := block_0_0x00b9(st); return st;} // fn 0x6fdde03 i.e. name()
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
		if st.PC() == 0x147 { st := block_0_0x0147(st); return st;} // fn 0x95ea7b3 i.e. approve(address,uint256)
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
		if st.PC() == 0x1a1 { st := block_0_0x01a1(st); return st;} // fn 0x18160ddd i.e. totalSupply()
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
		if st.PC() == 0x1ca { st := block_0_0x01ca(st); return st;} // fn 0x23b872dd i.e. transferFrom(address,address,uint256)
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
		if st.PC() == 0x243 { st := block_0_0x0243(st); return st;} // fn 0x2e1a7d4d ie. withdraw(uint256)
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
		if st.PC() == 0x266 { st := block_0_0x0266(st); return st;} // fn 0x313ce567 i.e. decimals()
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
		if st.PC() == 0x295 { st := block_0_0x0295(st); return st;} // fn 0x70a08231 ie. balanceOf(address)
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
		if st.PC() == 0x2e2 { st := block_0_0x02e2(st); return st;} // fn 0x95d89b41 i.e. symbol()
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
		if st.PC() == 0x370 { st := block_0_0x0370(st); return st;} //i.e. fn 0xa9059cbb transfer(address,uint256)
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
		if st.PC() == 0x3ca { st := block_0_0x03ca(st); return st;}  // i.e. fn 0xd0e30db0 deposit()
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
		if st.PC() == 0x3d4 { st := block_0_0x03d4(st); return st;} // fn 0xdd62ed3e allowance(address,address)
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
			assert st.evm.context.callValue == 0 ;
			st := block_0_0x01d5(st); 
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
		st := block_0_0x01f4(src, st);
		return st;
	}

	method block_0_0x01f4(src: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01f4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == src as u256 && st'.Peek(1) == 0x4 && st'.Peek(3) == 0x229)
	{
		var st := st';
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
		st := block_0_0x01fd(src,st);
		return st;
	}

	method block_0_0x01fd(src: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x01fd
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == st'.evm.context.CallDataRead(0x24) && st'.Peek(1) == 0x24 && st'.Peek(3) == src as u256 && st'.Peek(4) == 0x229)
	{
		var st := st';
		//|fp=0x0060|callData[0x24],0x24,0x04,src,0x229,transferFrom|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,dst,0x24,0x04,src,0x229,transferFrom|
		st := AndU160(st);
		//|fp=0x0060|dst,0x24,0x04,src,0x229,transferFrom| 
		var dst := st.Peek(0) as u160;
		assert dst as u256 == st.evm.context.CallDataRead(0x24) % (Int.TWO_160 as u256);

		st := Swap(st,1);
		//|fp=0x0060|0x24,dst,0x04,src,0x229,transferFrom|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x24,dst,0x04,src,0x229,transferFrom|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		assert st.Peek(5) == 0x229;
		st := Add(st);
		//|fp=0x0060|0x44,dst,0x04,src,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|dst,0x44,0x04,src,0x229,transferFrom|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x44,dst,src,0x229,transferFrom|
		st := Swap(st,1);
		//|fp=0x0060|0x44,0x04,dst,src,0x229,transferFrom|
		st := block_0_0x021a(src,dst,st);
		return st;
	}

	method block_0_0x021a(src: u160, dst: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x021a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x44 && st'.Peek(2) == dst as u256 && st'.Peek(3) == src as u256 && st'.Peek(4) == 0x229)
	{
		var st := st';
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
		st := block_0_0x0223(src,dst,wad,st);
		return st;
	}

	method block_0_0x0223(src: u160, dst: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0223
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(2) == wad && st'.Peek(3) == dst as u256 && st'.Peek(4) == src as u256 && st'.Peek(5) == 0x229)
	{
		var st := st';
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
		st := block_0_0x068c(src,dst,wad,st);
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
		if st.PC() == 0x24e { 
			assert st.evm.context.callValue == 0;
			st := block_0_0x024e(st); 
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
		var wad := st.Peek(0);
		assert wad == st.evm.context.CallDataRead(0x4);

		st := Swap(st,1);
		//|fp=0x0060|0x04,wad,0x04,0x264,callSig|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,wad,0x04,0x264,callSig|
		st := block_0_0x025a(wad,st);
		return st;
	}

	method block_0_0x025a(wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x025a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x4 && st'.Peek(2) == wad && st'.Peek(4) == 0x264)
	{
		var st := st';
		//|fp=0x0060|0x20,0x04,wad,0x04,0x264,callSig|
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
		st := block_0_0x09d9(wad,st);
		return st;
	}

	method block_0_0x0264(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0264
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
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

	method block_0_0x09d9(wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09d9
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == wad && st'.Peek(1) == 0x264)
	{
		var st := st';
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
		st := block_0_0x0a0b(wad,st);
		return st;
	}

	method block_0_0x0a0b(wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a0b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff && st'.Peek(2) == 0x0 
			&& st'.Peek(1) == st'.evm.context.sender as u256 && st'.Peek(3) == 0x03 && st'.Peek(4) == st'.Peek(5) == wad && st'.Peek(6) == 0x264)
	{
		var st := st';
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,wad,wad,0x264,callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,wad,wad,0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x00,0x03,wad,wad,0x264,callSig|
		st := MStore(st);
		assert {:split_here} true;
		assert (st.Peek(0) == 0x0 && st.Peek(1) == 0x03 && st.Peek(2) == st.Peek(3) && st.Peek(4) == 0x264);
		//|fp=0x0060|0x00,0x03,wad,wad,0x264,callSig| // st.Read(0x00) == caller
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,wad,wad,0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//assert {:split_here} true;
		//|fp=0x0060|0x20,0x03,wad,wad,0x264,callSig|
		assert (st.Peek(0) == 0x20 && st.Peek(1) == 0x03 && st.Peek(2) == st.Peek(3) == wad && st.Peek(4) == 0x264);
		st := block_0_0x0a11(wad,st);
		return st;
	}

	method block_0_0x0a11(wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a11
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x03 && st'.Peek(2) == st'.Peek(3) == wad && st'.Peek(4) == 0x264)
	{
		var st := st';	
		//|fp=0x0060|0x20,0x03,wad,wad,0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,wad,0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,wad,0x264,callSig|
		st := MStore(st);
		//|fp=0x0060|0x20,wad,wad,0x264,callSig| // st.Read(0x20) == 0x03
		assert st.Read(0x20) == 0x03;
		assert (st.Peek(0) == 0x20 && st.Peek(1) == st.Peek(2) == wad && st.Peek(3) == 0x264);
		st := block_0_0x0a14(wad,st);
		return st;
	}

	method block_0_0x0a14(wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a14
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == st'.Peek(2) == wad && st'.Peek(3) == 0x264)
	{
		var st := st';
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

		
		assert st.Peek(3) == 0x264;    
		//|fp=0x0060|hash,wad,wad,0x264,callSig|
		st := SLoad(st);
		//|fp=0x0060|bal,wad,wad,0x264,callSig|
		var bal := st.Peek(0);
		assert bal == st.Load(Hash(st.evm.context.sender as u256,0x03));
		
		assert st.Peek(1) == st.Peek(2);
		st := Lt(st);
		//|fp=0x0060|bal<wad,wad,0x264,callSig|
		assert if bal < st.Peek(1) then st.Peek(0) == 1 else st.Peek(0) == 0 ;
		st := IsZero(st);
		assert st.Peek(2) == 0x264;    
		//|fp=0x0060|{0,1},wad,0x264,callSig|
		st := IsZero(st);
		//|fp=0x0060|{1,0},wad,0x264,callSig|
		assert if bal < st.Peek(1) then st.Peek(0) == 1 else st.Peek(0) == 0;
		//assert st.Peek(2) == 0x264;
		st := block_0_0x0a1e(bal,wad,st);
		return st;
	}

	method block_0_0x0a1e(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a1e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(1)  == wad && st'.Peek(2) == 0x264)

	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))
	requires if bal < wad then st'.Peek(0) == 1 else st'.Peek(0) == 0
	{
		var st := st';
		//|fp=0x0060|{1,0},wad,0x264,callSig|
		st := IsZero(st);
		//|fp=0x0060|{0,1},wad,0x264,callSig|
		st := Push2(st,0x0a27);
		//|fp=0x0060|0xa27,{0,1},wad,0x264,callSig|
		assume {:axiom} st.IsJumpDest(0xa27);
		st := JumpI(st);
		if st.PC() == 0xa27 {  // i.e. bal>=wad
			assert st.Peek(0) == st'.Peek(1);
			assert bal >= wad;
			st := block_0_0x0a27(bal,wad,st); 
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

	method block_0_0x0a27(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a27
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == wad && st'.Peek(1) == 0x264)

	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))
	requires bal >= wad
	{
		var st := st';
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
		st := block_0_0x0a59(bal,wad,st);
		return st;
	}

	method block_0_0x0a59(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a59
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff && st'.Peek(1) == st'.evm.context.sender as u256 && 
			st'.Peek(2) == 0x0 && st'.Peek(3) == 0x03 && st'.Peek(4) == st'.Peek(5) == wad && st'.Peek(6) == 0x264)
	
	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))
	requires bal >= wad
	{
		var st := st';
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x00,0x03,wad,wad,0x264,callSig|
		st := AndU160(st);
		//|fp=0x0060|caller,0x00,0x03,wad,wad,0x264,callSig|
		assert st.Peek(0) == st.evm.context.sender as u256;
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x00,0x03,wad,wad,0x264,callSig|
		assert st.Peek(0) == 0x00;
		st := MStore(st);
		assert {:split_here} true;
		assert st.Read(0x00) == st.evm.context.sender as u256;
		assert (st.Peek(0) == 0x00 && st.Peek(1) == 0x03 && st.Peek(4) == 0x264);
		//|fp=0x0060|0x00,0x03,wad,wad,0x264,callSig| // st.Read(0x00) == caller
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,wad,wad,0x264,callSig|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		assert {:split_here} true;
		assert st.Read(0x00) == st.evm.context.sender as u256;
		assert (st.Peek(0) == 0x20 && st.Peek(1) == 0x03 && st.Peek(4) == 0x264);
		//|fp=0x0060|0x20,0x03,wad,wad,0x264,callSig|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,wad,0x264,callSig|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,wad,0x264,callSig|
		assert (st.Peek(0) == 0x20 && st.Peek(1) == 0x03 && st.Peek(2) == 0x20 && st.Peek(3) == st.Peek(4) == wad  && st.Peek(5) == 0x264);
		st := block_0_0x0a61(bal,wad,st);
		return st;
	}

	method block_0_0x0a61(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a61
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60  && st'.Read(0x00) == st'.evm.context.sender as u256 //&& st'.Read(0x20) == 0x03 
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x03 && st'.Peek(2) == 0x20 && st'.Peek(3) == st'.Peek(4) == wad && st'.Peek(5) == 0x264)

	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))
	requires bal >= wad
	{
		var st := st';
		//|fp=0x0060|0x20,0x03,0x20,wad,wad,0x264,callSig|
		st := MStore(st);
		//|fp=0x0060|0x20,wad,wad,0x264,callSig| // st.Read(0x20) == 0x03
		assert st.Read(0x00) == st.evm.context.sender as u256 && st.Read(0x20) == 0x03;
		assert st.Peek(1) == st.Peek(2) == wad;
		st := block_0_0x0a62(bal,wad,st);
		return st;
	}

	method block_0_0x0a62(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a62
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == st'.evm.context.sender as u256 && st'.Read(0x20) == 0x03 
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == st'.Peek(2) == wad && st'.Peek(3) == 0x264)
	
	requires bal == st'.Load(Hash(st'.evm.context.sender as u256,0x03))
	requires bal >= wad
	{
		var st := st';
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
		//|fp=0x0060|hash,wad,wad,0x264,callSig|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash,wad,wad,0x264,callSig|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x00,hash,wad,wad,0x264,callSig|
		st := Dup(st,3);
		//|fp=0x0060|hash,wad,0x00,hash,wad,wad,0x264,callSig|
		st := SLoad(st);
		//|fp=0x0060|bal,wad,0x00,hash,wad,wad,0x264,callSig|
		assert bal == st.Peek(0);
		st := block_0_0x0a6d(bal,wad,st);
		return st;
	}

	method block_0_0x0a6d(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a6d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x20) == 0x03 && st'.Read(0x00) == st'.evm.context.sender as u256
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(0) == bal && st'.Peek(1) == st'.Peek(4) == st'.Peek(5) == wad && st'.Peek(3) == Hash(st'.evm.context.sender as u256,0x03)  && st'.Peek(6) == 0x264)
	
	requires bal >= wad
	{
		var st := st';
		//|fp=0x0060|bal,wad,0x00,hash,wad,wad,0x264,callSig|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|bal-wad,0x00,hash,wad,wad,0x264,callSig|
		assert {:split_here} true;
		assert (st.Peek(4) == wad && st.Peek(5) == 0x264);

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
		assert {:split_here} true;
		assert st.Load(Hash(st.evm.context.sender as u256,0x03)) == bal - wad;
		assert (st.Peek(1) == wad && st.Peek(2) == 0x264);
		st := Pop(st);
		//|fp=0x0060|wad,0x264,callSig|
		st := block_0_0x0a75(bal,wad,st);
		return st;
	}

	method block_0_0x0a75(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State) 
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a75
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == wad && st'.Peek(1) == 0x264)
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
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
		st := block_0_0x0a93(bal,wad,st);
		return st;
	}

	method block_0_0x0a93(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a93
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires ((st'.Peek(0) == 0 || st'.Peek(0) == 1) && st'.Peek(1) == 0x8fc && st'.Peek(5) == 0x264)
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
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
		st := block_0_0x0a9e(bal,wad,st);
		return st;
	}

	method block_0_0x0a9e(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0a9e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(2) == 0x0 && st'.Peek(3) == 0x60 && st'.Peek(8) == 0x264) 
	requires st'.Peek(5) == 0 || st'.Peek(5) == 0x8fc
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
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
		//i.e wad != 0 ==> st.Peek(0) == 0 , wad == 0 ==> st.Peek(0) == 0x8fc
		assert st.Peek(12) == 0x264;
		var CONTINUING(cc) := Call(st);
		{
			var inner := cc.CallEnter(1);
			if inner.EXECUTING? { inner := external_call(cc.sender,inner); }
			st := cc.CallReturn(inner);
		}
		//|fp=0x0060|exitcode,0x60,wad,{0,0x8fc},caller,wad,0x264,_|
		assert st.Operands() == 8 && st.Peek(6) == 0x264;
		st := Swap(st,4);
		//|fp=0x0060|caller,0x60,wad,{0,0x8fc},exitCode,wad,0x264,_|
		assume st.Read(0x40) == 0x60;
		assume st.Load(Hash(st.evm.context.sender as u256,0x03)) == bal - wad; 
		
		st := block_0_0x0aa6(bal,wad,st);
		return st;
	}

	method block_0_0x0aa6(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0aa6
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires (st'.Peek(6) == 0x264)
	
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
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
			st := block_0_0x0ab4(bal,wad,st); 
			return st;
		}
		st := block_0_0x0ab0(st); // i.e. revert
		return st;
	}

	method block_0_0x0ab0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ab0
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	
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

	method block_0_0x0ab4(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0ab4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x264)

	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
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
		st := block_0_0x0af1(bal,wad,st);
		return st;
	}

	method block_0_0x0af1(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0af1
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(0) == 0x60 && st'.Peek(5) == 0x264)

	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		//|fp=0x0060|0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x60,0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,wad,0x60,0x60,wad,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := MStore(st);
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
		st := block_0_0x0afa(bal,wad,st);
		return st;
	}

	method block_0_0x0afa(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0afa
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires (st'.Peek(1) == 0x80 && st'.Peek(5) == 0x264)
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		//|fp=0x0060|0x60,0x80,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad],0x264,_|
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
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller,wad,0x264,_|
		st := LogN(st,2);
		//|fp=0x0060|wad,0x264,_| i.e. append to log (0x60,0x20,0x7fcf532c15f0a6dbbd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65,caller)
		st := block_0_0x0b03(bal,wad,st);
		return st;
	}

	method block_0_0x0b03(bal: u256, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b03
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(1) == 0x264)
	requires bal >= wad
	requires st'.Load(Hash(st'.evm.context.sender as u256,0x03)) == bal-wad
	{
		var st := st';
		//|fp=0x0060|wad,0x264,_|
		st := Pop(st);
		//|fp=0x0060|0x264,_|
		assume {:axiom} st.IsJumpDest(0x264);
		st := Jump(st);
		st := block_0_0x0264(bal,wad,st);
		return st;
	}

}
