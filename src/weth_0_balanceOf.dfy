include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module balanceOf {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header
	import opened Int

	method block_0_0x0295(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0295
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := CallValue(st);
		//|fp=0x0060|_,_|
		st := IsZero(st);
		//|fp=0x0060|_,_|
		st := Push2(st,0x02a0);
		//|fp=0x0060|0x2a0,_,_|
		assume {:axiom} st.IsJumpDest(0x2a0);
		st := JumpI(st);
		if st.PC() == 0x2a0 { st := block_0_0x02a0(st); return st;}
		//|fp=0x0060|_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,_|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,_|
		st := Revert(st);
		return st;
	}

	method block_0_0x02a0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02a0
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	{
		var st := st';
		//|fp=0x0060|_|
		st := JumpDest(st);
		//|fp=0x0060|_|
		st := Push2(st,0x02cc);
		//|fp=0x0060|0x2cc,_|
		st := Push1(st,0x04);
		//|fp=0x0060|0x04,0x2cc,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x2cc,_|
		st := Dup(st,1);
		//|fp=0x0060|0x04,0x04,0x04,0x2cc,_|
		st := CallDataLoad(st);
		//|fp=0x0060|_,0x04,0x04,0x2cc,_|
		st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
		//|fp=0x0060|0xffffffffffffffffffffffffffffffffffffffff,_,0x04,0x04,0x2cc,_|
		st := AndU160(st);

		var addr := st.Peek(0) as u160;
		assert addr as u256 == st.evm.context.CallDataRead(0x04) % (Int.TWO_160 as u256) ;
		st := block_0_0x02bf(addr,st);
		return st;
	}

	method block_0_0x02bf(addr: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02bf
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == addr as u256 && st'.Peek(1) == 0x4 && st'.Peek(3) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|addr,0x04,0x04,0x2cc,_|
		st := Swap(st,1);
		//|fp=0x0060|0x04,addr,0x04,0x2cc,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x04,addr,0x04,0x2cc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		//|fp=0x0060|0x20,0x04,addr,0x04,0x2cc,_|
		st := Add(st);
		//|fp=0x0060|0x24,addr,0x04,0x2cc,_|
		st := Swap(st,1);
		//|fp=0x0060|addr,0x24,0x04,0x2cc,_|
		st := Swap(st,2);
		//|fp=0x0060|0x04,0x24,addr,0x2cc,_|
		st := Swap(st,1);
		//|fp=0x0060|0x24,0x04,addr,0x2cc,_|
		st := Pop(st);
		//|fp=0x0060|0x04,addr,0x2cc,_|
		st := Pop(st);
		st := block_0_0x02c8(addr, st);
		return st;
	}

	method block_0_0x02c8(addr: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02c8
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == addr as u256 && st'.Peek(1) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|addr,0x2cc,_|
		st := Push2(st,0x0b18);
		//|fp=0x0060|0xb18,addr,0x2cc,_|
		assume {:axiom} st.IsJumpDest(0xb18);
		st := Jump(st);
		st := block_0_0x0b18(addr, st);
		return st;
	}

	method block_0_0x02cc(addr: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02cc
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == st'.Load(Hash(addr as u256,0x03)) && st'.Peek(1) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|balanceOf[addr],0x2cc,_|
		st := JumpDest(st);
		//|fp=0x0060|balanceOf[addr],0x2cc,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,balanceOf[addr],0x2cc,_|
		st := MLoad(st);
		//|fp=0x0060|0x60,balanceOf[addr],0x2cc,_| i.e. load fmp
		st := Dup(st,1);
		//|fp=0x0060|0x60,0x60,balanceOf[addr],0x2cc,_|
		st := Dup(st,3);
		//|fp=0x0060|balanceOf[addr],0x60,0x60,balanceOf[addr],0x2cc,_|
		st := Dup(st,2);
		//|fp=0x0060|0x60,balanceOf[addr],0x60,0x60,balanceOf[addr],0x2cc,_|
		st := MStore(st);
		//|fp=0x0060|0x60,0x60,balanceOf[addr],0x2cc,_| i.e. st.Read(0x60) == balanceOf[addr]
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x60,0x60,balanceOf[addr],0x2cc,_|
		st := block_0_0x02d6(addr, st);
		return st;
	}

	method block_0_0x02d6(addr: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02d6
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60 && st'.Read(0x60) == st'.Load(Hash(addr as u256,0x03))
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires (st'.Peek(0) == 0x20 && st'.Peek(1) == 0x60)
	{
		var st := st';
		//|fp=0x0060|0x20,0x60,0x60,balanceOf[addr],0x2cc,_|
		assert (st.Peek(0) + st.Peek(1)) <= (Int.MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|0x80,0x60,balanceOf[addr],0x2cc,_|
		st := Swap(st,2);
		//|fp=0x0060|balanceOf[addr],0x60,0x80,0x2cc,_|
		st := Pop(st);
		//|fp=0x0060|0x60,0x80,0x2cc,_|
		st := Pop(st);
		//|fp=0x0060|0x80,0x2cc,_|
		st := Push1(st,0x40);
		//|fp=0x0060|0x40,0x80,0x2cc,_|
		st := MLoad(st);
		//|fp=0x0060|fmp==0x60,0x80,0x2cc,_|
		st := Dup(st,1);
		//|fp=0x0060|fmp==0x60,fmp==0x60,0x80,0x2cc,_|
		st := Swap(st,2);
		st := block_0_0x02df(addr, st);
		return st;
	}

	method block_0_0x02df(addr: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02df
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0x60 && st'.Read(0x60) == st'.Load(Hash(addr as u256,0x03))
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires (st'.Peek(0) == 0x80 && st'.Peek(1) == 0x60 && st'.Peek(2) == 0x60) // == balanceOf[addr]
	
	ensures st''.RETURNS? && st''.data == Int.ToBytes(st'.Load(Hash(addr as u256,0x03)) as nat) 
	{
		var st := st';
		//|fp=0x0060|0x80,fmp==0x60,fmp==0x60,0x2cc,_|
		assert st.Peek(1) <= st.Peek(0);
		//|fp=0x0060|0x80,fmp==0x60,fmp==0x60,0x2cc,_|
		st := Sub(st);
		//|fp=0x0060|0x20,fmp==0x60,0x2cc,_|
		st := Swap(st,1);
		//|fp=0x0060|fmp==0x60,0x20,0x2cc,_|
		//assume {:axiom} Memory.Slice(st.evm.memory, 0x60, 0x20) == Int.ToBytes(st.Read(0x60) as nat);
		MemoryReadAxiom(st,0x60);
		st := Return(st); 
		return st;
	}

	method block_0_0x0b18(addr: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b18
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == addr as u256 && st'.Peek(1) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|addr,0x2cc,_|
		st := JumpDest(st);
		//|fp=0x0060|addr,0x2cc,_|
		st := Push1(st,0x03);
		//|fp=0x0060|0x03,addr,0x2cc,_|
		st := Push1(st,0x20);
		//|fp=0x0060|0x20,0x03,addr,0x2cc,_|
		assert st.Peek(1) == 0x03;
		st := MStore(st);
		assert {:split_here} true;
		assert st.Peek(0) == addr as u256 && st.Peek(1) == 0x2cc;
		//|fp=0x0060|addr,0x2cc,_| i.e. st.Read(0x20) == 0x03
		st := Dup(st,1);
		//|fp=0x0060|addr,addr,0x2cc,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,addr,addr,0x2cc,_| 
		st := MStore(st);
		assert {:split_here} true;
		assert st.Peek(0) == addr as u256 && st.Peek(1) == 0x2cc;
		//|fp=0x0060|addr,0x2cc,_| i.e. st.Read(0x00) == addr
		st := Push1(st,0x40);
		st := block_0_0x0b24(addr,st);
		return st;
	}

	method block_0_0x0b24(addr: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b24
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60 && st'.Read(0x00) == addr as u256 && st'.Read(0x20) == 0x03
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires (st'.Peek(0) == 0x40 && st'.Peek(1) == addr as u256 && st'.Peek(2) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|0x40,addr,0x2cc,_|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,0x40,addr,0x2cc,_|
		st := Keccak256(st);
		//|fp=0x0060|hash,addr,0x2cc,_|
		HashEquivalenceAxiom(st,st.Peek(0),addr as u256,0x03);
		assert st.Peek(0) == Hash(addr as u256,0x03);

		st := Push1(st,0x00);
		//|fp=0x0060|0x00,hash,addr,0x2cc,_|
		st := Swap(st,2);
		//|fp=0x0060|addr,hash,0x00,0x2cc,_|
		st := Pop(st);
		//|fp=0x0060|hash,0x00,0x2cc,_|
		st := Swap(st,1);
		//|fp=0x0060|0x00,hash,0x2cc,_|
		st := Pop(st);
		//|fp=0x0060|hash,0x2cc,_|
		st := SLoad(st);
		//|fp=0x0060|balanceOf[addr],0x2cc,_|
		
		assert st.Peek(0) == st.Load(Hash(addr as u256,0x03));
		
		st := block_0_0x0b2e(addr,st);
		return st;
	}

	method block_0_0x0b2e(addr: u160, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b2e
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires (st'.Peek(0) == st'.Load(Hash(addr as u256,0x03)) && st'.Peek(1) == 0x2cc)
	{
		var st := st';
		//|fp=0x0060|balanceOf[addr],0x2cc,_|
		st := Dup(st,2);
		//|fp=0x0060|0x2cc,balanceOf[addr],0x2cc,_|
		assume {:axiom} st.IsJumpDest(0x2cc);
		st := Jump(st);
		st := block_0_0x02cc(addr,st);
		return st;
	}

}
