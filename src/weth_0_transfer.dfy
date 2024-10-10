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
	method block_0_0x0370(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0370
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires 0xa9059cbb == callSig
	requires st'.evm.stack.contents == [callSig]

	ensures st'.evm.context.callValue != 0 ==> st''.IsRevert()
	{
		var st := st';
		stackLemma(st,st.Operands());
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
		if st.PC() == 0x37b { 
			// call value is zero
			stackLemma(st,st.Operands());
			st := block_0_0x037b(callSig,st); 
			return st;
		} // call value == 0
		//|fp=0x0060|transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,transfer|
		st := Revert(st); //i.e. revert is call value != 0 
		return st;
	}

	method block_0_0x037b(callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x037b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	requires 0xa9059cbb == callSig
	requires st'.evm.stack.contents == [callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
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
		stackLemma(st,st.Operands());
		st := block_0_0x039a(dst,callSig,st);
		return st;
	}

	method block_0_0x039a(dst: u160, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x039a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	requires 0xa9059cbb == callSig
	// Static stack items
	requires st'.evm.stack.contents == [dst as u256,0x04,st'.Peek(2),0x3b0,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
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
		stackLemma(st,st.Operands());
		st := block_0_0x03a3(dst,wad,callSig,st);
		return st;
	}

	method block_0_0x03a3(dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03a3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	requires 0xa9059cbb == callSig
	// Static stack items
	requires st'.evm.stack.contents == [wad,0x24,st'.Peek(2),dst as u256,0x3b0,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
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
		stackLemma(st,st.Operands());
		st := block_0_0x03ac(dst,wad,callSig,st);
		return st;
	}

	method block_0_0x03ac(dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03ac
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	requires 0xa9059cbb == callSig
	// Static stack items
	requires st'.evm.stack.contents == [wad,dst as u256,0x3b0,callSig]
	
	requires (st'.Peek(2) == 0x3b0)
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,dst,0x3b0,transfer|
		st := Push2(st,0x0bce);
		//|fp=0x0060|0xbce,wad,dst,0x3b0,transfer|
		assume {:axiom} st.IsJumpDest(0xbce);
		st := Jump(st);
		//|fp=0x0060|wad,dst,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_0_0x0bce(dst,wad,callSig,st);
		return st;
	}


	method block_0_0x03b0(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03b0
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	requires 0xa9059cbb == callSig
	requires st'.evm.stack.contents == [st'.Peek(0),callSig]

	requires src == st'.evm.context.sender
	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x01,transfer|
		st := JumpDest(st);
		//|fp=0x0060|0x01,transfer|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x01,transfer|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x01,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x01,transfer|
		st := Dup(st,3);
		//|fp=0x0060|0x01,0x60,0x60,0x01,transfer|
		st := IsZero(st);
		//|fp=0x0060|0x00,0x60,0x60,0x01,transfer|
		st := IsZero(st);
		//|fp=0x0060|0x01,0x60,0x60,0x01,transfer|
		st := IsZero(st);
		//|fp=0x0060|0x0,0x60,0x60,0x01,transfer|
		stackLemma(st,st.Operands());
		st := block_0_0x03b9(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x03b9(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03b9
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [st'.Peek(0),0x60,st'.Peek(2),st'.Peek(3),callSig]
	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,0x60,0x60,0x01,transfer|
		st := IsZero(st);
		//|fp=0x0060|0x1,0x60,0x60,0x01,transfer|
		st := Dup(st,2);
		//|fp=0x0060|0x60,0x01,0x60,0x60,0x01,transfer|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,0x01,transfer|
		stackLemma(st,st.Operands());
		st := block_0_0x03bc(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x03bc(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03bc
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x60,st'.Peek(1),st'.Peek(2),callSig]
	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x60,0x01,transfer|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,0x01,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,0x01,transfer|
		st := Swap(st,2);
		//|fp=0x0060|0x01,0x60,0x80,transfer|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,transfer|
		st := Pop(st);
		//|fp=0x0060|0x80,transfer|
		stackLemma(st,st.Operands());
		st := block_0_0x03c2(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x03c2(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x03c2
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x80,callSig]
	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x80,transfer|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,transfer|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,transfer|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,transfer|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,0x60,0x60,transfer|
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,transfer|
		st := Return(st);
		return st;
	}

	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	// from (transfer) bce: 		|fp=0x0060|wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 	& call value == 0 
	// NB: when 'transfer' a source isn't specified, instead we set src == caller

	method block_1_0x068c(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x068c
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 9
	requires 0xa9059cbb == callSig
	// Dynamic stack items
	requires st'.evm.stack.contents == [wad,dst as u256,src as u256,0xbdb,st'.Peek(4),st'.Peek(5),st'.Peek(6),0x3b0,callSig] 
	requires src == st'.evm.context.sender
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := JumpDest(st);
		//|fp=0x0060|wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,7);
		//|fp=0x0060|caller,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|caller*,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x06ab(src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x06ab(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06ab
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 14
	requires 0xa9059cbb == callSig
	// Stack items
	requires st'.evm.stack.contents == [src as u256,0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(9),st'.Peek(10),st'.Peek(11),0x3b0,callSig] 
	requires src == st'.evm.context.sender
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|caller*,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller*,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|caller*,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Peek(0) == src as u256 == st.evm.context.sender as u256;
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller*,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := MStore(st);
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 	i.e.st.Read(0x0) == caller*
		stackLemma(st,st.Operands());
		st := block_1_0x06c3(src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x06c3(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06c3
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() == 13
	requires 0xa9059cbb == callSig
	// Stack items
	requires st'.evm.stack.contents == [0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(8),st'.Peek(9),st'.Peek(10),0x3b0,callSig] 
	requires src == st'.evm.context.sender
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x06c8(src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x06c8(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06c8
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() == 14
	requires 0xa9059cbb == callSig
	// Stack items
	requires st'.evm.stack.contents == [0x20,0x03,0x20,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(9),st'.Peek(10),st'.Peek(11),0x3b0,callSig] 
	requires src == st'.evm.context.sender
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x03,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_1_0x06c9(src,dst,wad,callSig,st);
		return st;
	}
	
	method block_1_0x06c9(src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06c9
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 12
	requires 0xa9059cbb == callSig
	// Stack items
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(7),st'.Peek(8),st'.Peek(9),0x3b0,callSig] 
	requires src == st'.evm.context.sender
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| i.e. st.Read(0x20) == 0x03
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x40,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Keccak256(st);
		//|fp=0x0060|hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 		// i.e hash == Keccak(...0x0,0x40)
		HashEquivalenceAxiom(st,st.Peek(0),src as u256,0x03);
		assert st.Peek(0) == Hash(src as u256,0x03);
		assert st.evm.stack.contents == [Hash(src as u256,0x03),wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(7),st'.Peek(8),st'.Peek(9),0x3b0,callSig]; 
		st := SLoad(st);
		//|fp=0x0060|bal,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		var bal := st.Peek(0);
		assert bal == st.Load(Hash(src as u256,0x03));
		st := Lt(st);
		//|fp=0x0060|bal < wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		//assert st.Peek(0) == (if bal < wad then 1 else 0);
		st := IsZero(st);
		//|fp=0x0060|bal < wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		//assert (st.Peek(0) == (if bal < wad then 0 else 1) );
		stackLemma(st,st.Operands());
		st := block_1_0x06d2(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x06d2(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06d2
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	requires 0xa9059cbb == callSig
	// Stack items
	requires st'.Peek(0) == if bal < wad then 0 else 1
	requires  st'.evm.stack.contents == [st'.Peek(0),0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(6),st'.Peek(7),st'.Peek(8),0x3b0,callSig] 
	// Storage
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires src == st'.evm.context.sender
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|{1,0},0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := IsZero(st);
		//|fp=0x0060|{0,1},0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := IsZero(st);
		//|fp=0x0060|{1,0},0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push2(st,0x06dc);
		//|fp=0x0060|0x06dc,{1,0},0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assume {:axiom} st.IsJumpDest(0x6dc);
		st := JumpI(st);
		if st.PC() == 0x6dc { 
			// i.e. bal >= wad
			//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
			stackLemma(st,st.Operands());
			st := block_1_0x06dc(bal,src,dst,wad,callSig,st); 
			return st;
		} 
 		//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x0,0x0,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Revert(st); // i.e. balOfCaller (or balOfSrc) < wad
		return st;
	}

	method block_1_0x06dc(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x06dc
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	requires 0xa9059cbb == callSig
	// Stack items
	requires st'.evm.stack.contents == [0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(5),st'.Peek(6),st'.Peek(7),0x3b0,callSig] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))

	requires src == st'.evm.context.sender
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| // i.e. balOfCaller (or balOfSrc) >= wad
		st := JumpDest(st);
		//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 
		st := Caller(st);
		//|fp=0x0060|caller,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|caller*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 
		st := Dup(st,5);
		//|fp=0x0060|caller,caller*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,caller*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|caller*,caller*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 
		st := Eq(st);
		//|fp=0x0060|caller* == caller*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 
		stackLemma(st,st.Operands());
		st := block_1_0x070c(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x070c(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x070c
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	requires 0xa9059cbb == callSig
	// Stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x1,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(6),st'.Peek(7),st'.Peek(8),0x3b0,callSig] 
					
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|caller == caller,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 
		st := IsZero(st);
		//|fp=0x0060|src != caller,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|  i.e. should always be true!!
		st := Dup(st,1);
		//|fp=0x0060|src != caller,src != caller,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|  
		st := IsZero(st);
		//|fp=0x0060|src == caller,src != caller,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|  
		st := Push2(st,0x07b4);
		//|fp=0x0060|0x7b4,src == caller,src != caller,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assume {:axiom} st.IsJumpDest(0x7b4);
		st := JumpI(st);
		if st.PC() == 0x7b4 { 
			// src == caller
			stackLemma(st,st.Operands());
			st := block_1_0x07b4(bal,src,dst,wad,callSig,st); 
			return st;
		}
		assert false;
		// //|fp=0x0060|0x1,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| // i.e. this path shouldn't be possible!! (caller != src)
		// st := Pop(st);
		// //|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 
		// st := PushN(st,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
		// //|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		// st := Push1(st,0x04);
		// //|fp=0x0060|0x04,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		// stackLemma(st,st.Operands());
		// st := block_1_0x0737(bal,src,dst,wad,st);
		// return st;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	//from 7ae: |fp=0x0060|{0,1},0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| (i.e. shouldn't be possible from 7ae)
	//from 70c: |fp=0x0060|0x0,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer| 


	method block_1_0x07b4(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x07b4
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	requires 0xa9059cbb == callSig
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x0,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(6),st'.Peek(7),st'.Peek(8),0x3b0,callSig] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := JumpDest(st);
		//|fp=0x0060|0,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := IsZero(st);
		//|fp=0x0060|1,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push2(st,0x08cf);
		//|fp=0x0060|0x8cf,1,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assume {:axiom} st.IsJumpDest(0x8cf);
		st := JumpI(st);
		if st.PC() == 0x8cf { 
			stackLemma(st,st.Operands());
			st := block_1_0x08cf(bal,src,dst,wad,callSig,st); 
			return st;
		} 
		assert false;
		// //|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		// st := Dup(st,2);
		// //|fp=0x0060|wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		// st := Push1(st,0x04);
		// //|fp=0x0060|0x04,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		// st := Push1(st,0x00);
		// //|fp=0x0060|0x0,0x04,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		// st := Dup(st,7);
		// //|fp=0x0060|caller,0x0,0x04,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		// stackLemma(st,st.Operands());
		// st := block_1_0x07c0(bal,src,dst,wad,st);
		// return st;
	}

	method block_1_0x08cf(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x08cf
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	requires 0xa9059cbb == callSig
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(5),st'.Peek(6),st'.Peek(7),0x3b0,callSig] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := JumpDest(st);
		//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfe|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfe|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfe|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfe|
		st := Dup(st,7);
		//|fp=0x0060|caller,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|caller,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Peek(0) == src as u256;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x0901(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x0901(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0901
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 
	// Stack height(s)
	requires st'.Operands() == 15
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0xffffffffffffffffffffffffffffffffffffffff,src as u256,0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(10),st'.Peek(11),st'.Peek(12),0x3b0,callSig] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|caller,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Peek(0) == src as u256;
		st := Dup(st,2);
		//|fp=0x0060|0x00,caller,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := MStore(st);
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x0904(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x0904(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0904
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256
	// Stack height(s)
	requires st'.Operands() == 13
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(8),st'.Peek(9),st'.Peek(10),0x3b0,callSig] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x0,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := block_1_0x0909(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x0909(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0909
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 
	// Stack height(s)
	requires st'.Operands() == 14
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x20,0x03,0x20,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(9),st'.Peek(10),st'.Peek(11),0x3b0,callSig] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());	
		//|fp=0x0060|0x20,0x03,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := MStore(st);
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x090a(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x090a(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x090a
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == src as u256 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 12
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x20,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(7),st'.Peek(8),st'.Peek(9),0x3b0,callSig] 
	
	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Keccak256(st);
		//|fp=0x0060|hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		HashEquivalenceAxiom(st,st.Peek(0),src as u256,0x03);
		assert st.Peek(0) == Hash(src as u256,0x03);
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x00,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,3);
		//|fp=0x0060|hash,wad,0x00,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := SLoad(st);
		//|fp=0x0060|Load(hash),wad,0x00,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		assert st.evm.stack.contents == [bal,wad,0x0,Hash(src as u256,0x03),wad,0x0,wad,dst as u256,src as u256,0xbdb,st.Peek(10),st.Peek(11),st.Peek(12),0x3b0,st.Peek(14)] ;
		st := block_1_0x0915(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x0915(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0915
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 15
	requires 0xa9059cbb == callSig
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [bal,wad,0x0,Hash(src as u256,0x03),wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(10),st'.Peek(11),st'.Peek(12),0x3b0,callSig] 

	requires bal >= wad
	requires bal == st'.Load(Hash(src as u256,0x03))
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|Load(hash),wad,0x00,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|Load(hash)-wad,0x00,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,3);
		//|fp=0x0060|wad,0x00,hash,Load(hash)-wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|0x00,hash,Load(hash)-wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|hash,Load(hash)-wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,2);
		//|fp=0x0060|Load(hash)-wad,hash,Load(hash)-wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|hash,Load(hash)-wad,Load(hash)-wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := SStore(st);
		//|fp=0x0060|Load(hash)-wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Load(Hash(src as u256,0x03)) == bal - wad;
		st := Pop(st);
		//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x091d(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x091d(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x091d
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 10
	requires 0xa9059cbb == callSig
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(5),st'.Peek(6),st'.Peek(7),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,2);
		//|fp=0x0060|wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,6);
		//|fp=0x0060|dst*,0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,dst*,0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|dst*,0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Peek(0) == dst as u256 ;
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,dst*,0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|dst*,0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Peek(0) == dst as u256 ;
		st := Dup(st,2);
		//|fp=0x0060|0x0,dst*,0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		assert st.evm.stack.contents == [0x0,dst as u256,0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0xbdb,st.Peek(10),st.Peek(11),st.Peek(12),0x3b0,st.Peek(14)] ;
		st := block_1_0x0950(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x0950(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0950
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 15
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x0,dst as u256,0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(10),st'.Peek(11),st'.Peek(12),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x0,dst*,0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := MStore(st);
		//|fp=0x0060|0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x0951(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x0951(bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0951
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == dst as u256
	// Stack height(s)
	requires st'.Operands() == 13
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x0,0x03,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(8),st'.Peek(9),st'.Peek(10),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x00,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x20,0x03,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x03,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,2);
		//|fp=0x0060|0x20,0x03,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x0956(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x0956(bal: u256,src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0956
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == dst as u256 
	// Stack height(s)
	requires st'.Operands() == 14
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x20,0x03,0x20,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(9),st'.Peek(10),st'.Peek(11),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);
		//|fp=0x0060|0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x0959(bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x0959(bal: u256,src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0959
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x0) == dst as u256 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 13
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x20,0x20,wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(8),st'.Peek(9),st'.Peek(10),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x20,0x20,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x40,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,0x40,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Keccak256(st);
		//|fp=0x0060|hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		HashEquivalenceAxiom(st,st.Peek(0),dst as u256,0x03);
		assert st.Peek(0) == Hash(dst as u256,0x03);
		st := Push1(st,0x00);
		//|fp=0x0060|0x0,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x0,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,3);
		//|fp=0x0060|hash,wad,0x0,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := SLoad(st);
		//|fp=0x0060|Load(hash),wad,0x0,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		var dBal := st.Peek(0);
		assert dBal == st.Load(Hash(dst as u256,0x03));

		TotalSupplyBoundAxiom(st.Peek(0),st.Peek(1));
		assert (st.Peek(0) as nat + st.Peek(1) as nat) <= (Int.MAX_U256 ); 
		st := Add(st);
		//|fp=0x0060|Load(hash)+wad,0x0,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x0963(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x0963(dBal: u256, bal: u256,src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0963
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 14
	requires 0xa9059cbb == callSig
	requires src == st'.evm.context.sender

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) == dBal

	requires st'.Peek(0) as nat == dBal as nat + wad as nat <= Int.MAX_U256 
	requires st'.evm.stack.contents == [st'.Peek(0),0x0,Hash(dst as u256,0x03),wad,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(9),st'.Peek(10),st'.Peek(11),0x3b0,callSig] 

	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|Load(hash)+wad,0x0,hash,wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,3);
		//|fp=0x0060|wad,0x0,hash,Load(hash)+wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|0x0,hash,Load(hash)+wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|hash,Load(hash)+wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,2);
		//|fp=0x0060|Load(hash)+wad,hash,Load(hash)+wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|hash,Load(hash)+wad,Load(hash)+wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := SStore(st);
		//|fp=0x0060|Load(hash)+wad,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,3);
		//|fp=0x0060|dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		NoCollisionsAxiom(Hash(dst as u256,0x03),Hash(src as u256,0x03));
		stackLemma(st,st.Operands());
		st := block_1_0x096b(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x096b(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x096b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 11
	requires 0xa9059cbb == callSig
	requires src == st'.evm.context.sender

	requires st'.evm.stack.contents == [dst as u256,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(6),st'.Peek(7),st'.Peek(8),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Peek(0) == dst as u256 ;
		st := Dup(st,5);
		//|fp=0x0060|caller,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,caller,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := AndU160(st);
		//|fp=0x0060|caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Peek(0) == src as u256 ;
		st := PushN(st,32,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
		//|fp=0x0060|0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,5);
		//|fp=0x0060|wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x09bc(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x09bc(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09bc
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 15
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x40,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src as u256,dst as u256,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(10),st'.Peek(11),st'.Peek(12),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x40,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := MLoad(st);
		//|fp=0x0060|0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,3);
		//|fp=0x0060|wad,0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,2);
		//|fp=0x0060|0x60,wad,0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x09c1(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x09c1(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09c1
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x60) == wad
	// Stack height(s)
	requires st'.Operands() == 16
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src as u256,dst as u256,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(11),st'.Peek(12),st'.Peek(13),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,wad,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,2);
		//|fp=0x0060|wad,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x09c5(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x09c5(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09c5
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 //&& st'.Read(0x60) == wad
	// Stack height(s)
	requires st'.Operands() == 16
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [wad,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src as u256,dst as u256,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(11),st'.Peek(12),st'.Peek(13),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|wad,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := MLoad(st);
		//|fp=0x0060|0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,0x80,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,2);
		//|fp=0x0060|0x80,0x60,0x60,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|0x20,0x60,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x60,0x20,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x09ce(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x09ce(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09ce
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 15
	requires 0xa9059cbb == callSig
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [0x60,0x20,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,src as u256,dst as u256,0x0,wad,dst as u256,src as u256,0xbdb,st'.Peek(10),st'.Peek(11),st'.Peek(12),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x60,0x20,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,caller*,dst*,0x0,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := LogN(st,3);
		//|fp=0x0060|0x00,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,0x00,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x0,0x01,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|0x01,wad,dst*,caller,0xbdb,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,4);
		//|fp=0x0060|0xbdb,wad,dst*,caller,0x01,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,3);
		//|fp=0x0060|caller,wad,dst*,0xbdb,0x01,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|wad,dst*,0xbdb,0x01,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|dst*,0xbdb,0x01,0x00,wad,dst*,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x09d7(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}

	method block_1_0x09d7(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x09d7
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 8
	requires 0xa9059cbb == callSig
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [dst as u256,0xbdb,0x01,st'.Peek(3),st'.Peek(4),st'.Peek(5),0x3b0,callSig] 

	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|dst*,0xbdb,0x01,0x00,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|0xbdb,0x01,0x00,wad,dst*,0x3b0,transfer|
		assume {:axiom} st.IsJumpDest(0xbdb);
		st := Jump(st);
		stackLemma(st,st.Operands()); 
		st := block_0_0x0bdb(dBal,bal,src,dst,wad,callSig,st); 
		return st;
	}


	method block_0_0x0bce(dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bce
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	requires 0xa9059cbb == callSig
	// Static stack items
	requires st'.evm.stack.contents == [wad,dst as u256,0x3b0,callSig]
	{
		var st := st';
		stackLemma(st,st.Operands());
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
		//assert caller == st.evm.context.sender;
		st := Dup(st,5);
		//|fp=0x0060|dst,caller,0xbdb,0x00,wad,dst,0x3b0,transfer|
		st := Dup(st,5);
		//|fp=0x0060|wad,dst,caller,0xbdb,0x00,wad,dst,0x3b0,transfer|
		st := Push2(st,0x068c);
		//|fp=0x0060|0x68c,wad,dst,caller,0xbdb,0x00,wad,dst,0x3b0,transfer|
		assume {:axiom} st.IsJumpDest(0x68c);
		st := Jump(st);
		//|fp=0x0060|wad,dst,caller,0xbdb,0x00,wad,dst,0x3b0,transfer|
		stackLemma(st,st.Operands());
		st := block_1_0x068c(caller,dst,wad,callSig,st);
		return st;
	}

	method block_0_0x0bdb(dBal: u256, bal: u256, src: u160, dst: u160, wad: u256, callSig: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bdb
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	requires 0xa9059cbb == callSig
	// Static stack items
	requires src == st'.evm.context.sender
	requires st'.evm.stack.contents == [st'.Peek(0),st'.Peek(1),st'.Peek(2),st'.Peek(3),0x3b0,callSig] 
	requires bal >= wad
	requires st'.Load(Hash(src as u256,0x03)) == bal-wad
	requires st'.Load(Hash(dst as u256,0x03)) as nat == dBal as nat + wad as nat 
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x01,0x00,wad,dst*,0x3b0,transfer|
		st := JumpDest(st);
		//|fp=0x0060|0x01,0x00,wad,dst*,0x3b0,transfer|
		st := Swap(st,1);
		//|fp=0x0060|0x0,0x01,wad,dst*,0x3b0,transfer|
		st := Pop(st);
		//|fp=0x0060|0x01,wad,dst*,0x3b0,transfer|
		st := Swap(st,3);
		//|fp=0x0060|0x3b0,wad,dst*,0x01,transfer|
		st := Swap(st,2);
		//|fp=0x0060|dst*,wad,0x3b0,0x01,transfer|
		st := Pop(st);
		//|fp=0x0060|wad,0x3b0,0x01,transfer|
		st := Pop(st);
		//|fp=0x0060|0x3b0,0x01,transfer|
		assume {:axiom} st.IsJumpDest(0x3b0);
		st := Jump(st);
		//|fp=0x0060|0x01,transfer|
		stackLemma(st,st.Operands());
		st := block_0_0x03b0(dBal,bal,src,dst,wad,callSig,st);
		return st;
	}


}
