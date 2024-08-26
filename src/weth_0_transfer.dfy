include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"
include "weth_0_util.dfy"

module transfer {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header
	import opened util
	import opened Int

	//i.e. fn 0xa9059cbb transfer(dstess,uint256)
	method block_0_0x0370(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0370
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|transfer|
		st := JumpDest(st);
		//|fp=0x0060|transfer|
		st := CallValue(st);
		//|fp=0x0060|callVal,transfer|
		st := IsZero(st);
		//|fp=0x0060|callVal==0,transfer|
		st := Push2(st,0x037b);
		//|fp=0x0060|0x37b,callVal==0,transfer|
		assume {:axiom} st.IsJumpDest(0x37b);
		st := JumpI(st);
		if st.PC() == 0x37b { st := block_0_0x037b(st); return st;} // call value == 0
		//|fp=0x0060|transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,transfer|
		st := Revert(st); //i.e. revert is call value != 0 
		return st;
	}

	method block_0_0x037b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x037b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|transfer|
		st := JumpDest(st);
		//|fp=0x0060|transfer|
		st := Push2(st,0x03b0);
		//|fp=0x0060|0x3b0,transfer|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,0x3b0,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x3b0,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x04,0x3b0,transfer|
		st := CallDataLoad(st);
		//|fp=0x0060|dst,0x04,0x04,0x3b0,transfer|   i.e. address from callData[0x4] == parm0 == dst dst
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,dst,0x04,0x04,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|dst,0x04,0x04,0x3b0,transfer|  
		var dst := st.Peek(0) as u160;
		assert dst as u256 == st.evm.context.CallDataRead(0x4) % (Int.TWO_160 as u256);

		st := block_0_0x039a(dst,st);
		return st;
	}

	method block_0_0x039a(dst: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x039a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == dst as u256 && st'.Peek(1) == 0x4 && st'.Peek(3) == 0x3b0)
	{
		var st := st';
		//|fp=0x0060|dst,0x04,0x04,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x04,dst,0x04,0x3b0,transfer|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,dst,0x04,0x3b0,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x24,dst,0x04,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|dst,0x24,0x04,0x3b0,transfer|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,dst,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,dst,0x3b0,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x24,0x24,0x04,dst,0x3b0,transfer|
		st := CallDataLoad(st);
		//|fp=0x0060|wad,0x24,0x04,dst,0x3b0,transfer| i.e. data[0x24] == parm1 == wad u256
		var wad := st.Peek(0);
		assert wad == st.evm.context.CallDataRead(0x24);

		assert st.Peek(3) == dst as u256;
		st := block_0_0x03a3(dst,wad,st);
		return st;
	}

	method block_0_0x03a3(dst: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03a3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == wad && st'.Peek(1) == 0x24 && st'.Peek(3) == dst as u256 && st'.Peek(4) == 0x3b0)
	{
		var st := st';
		//|fp=0x0060|wad,0x24,0x04,dst,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x24,wad,0x04,dst,0x3b0,transfer|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x24,wad,0x04,dst,0x3b0,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x44,wad,0x04,dst,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|wad,0x44,0x04,dst,0x3b0,transfer|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x44,wad,dst,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x44,0x04,wad,dst,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|0x04,wad,dst,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|wad,dst,0x3b0,transfer|
		st := block_0_0x03ac(dst,wad,st);
		return st;
	}

	method block_0_0x03ac(dst: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03ac
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x3b0)
	{
		var st := st';
		//|fp=0x0060|wad,dst,0x3b0,transfer|
		st := Push2(st,0x0bce);
		//|fp=0x0060|0xbce,wad,dst,0x3b0,transfer|
		assume {:axiom} st.IsJumpDest(0xbce);
		st := Jump(st);
		//|fp=0x0060|wad,dst,0x3b0,transfer|
		st := block_0_0x0bce(dst,wad,st);
		return st;
	}

	method block_0_0x0bce(dst: u160, wad: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bce
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(2) == 0x3b0)
	{
		var st := st';
		//|fp=0x0060|wad,dst,0x3b0,transfer|
		st := JumpDest(st);
		//|fp=0x0060|wad,dst,0x3b0,transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,wad,dst,0x3b0,transfer|
		st := Push2(st,0x0bdb);
		//|fp=0x0060|0xbdb,0x00,wad,dst,0x3b0,transfer|
		st := Caller(st);
		//|fp=0x0060|caller,0xbdb,0x00,wad,dst,0x3b0,transfer|
		var caller := st.Peek(0) as u160;
		assert caller == st.evm.context.sender;

		st := Dup(st,5);
		//|fp=0x0060|dst,caller,0xbdb,0x00,wad,dst,0x3b0,transfer|
		st := Dup(st,5);
		//|fp=0x0060|wad,dst,caller,0xbdb,0x00,wad,dst,0x3b0,transfer|
		st := Push2(st,0x068c);
		//|fp=0x0060|0x68c,wad,dst,caller,0xbdb,0x00,wad,dst,0x3b0,transfer|
		assume {:axiom} st.IsJumpDest(0x68c);
		st := Jump(st);
		//|fp=0x0060|wad,dst,caller,0xbdb,0x00,wad,dst,0x3b0,transfer|
		st := block_0_0x068c(caller,dst,wad,st);
		return st;
	}

}
