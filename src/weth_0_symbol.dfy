include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "weth_0_header.dfy"

module symbol {
	import opened Opcode
	import opened Code
	import opened Memory
	import opened Bytecode
	import opened Header

	method block_0_0x02e2(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02e2
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x95d89b41| // fn 0x95d89b41 "symbol()"
		st := JumpDest(st);
		//|fp=0x0060|symbol|
		st := CallValue(st);
		//|fp=0x0060|callVal,symbol|
		st := IsZero(st);
		//|fp=0x0060|callVal==0,symbol|
		st := Push2(st,0x02ed);
		//|fp=0x0060|0x2ed,callVal==0,symbol|
		assume {:axiom} st.IsJumpDest(0x2ed);
		st := JumpI(st);
		if st.PC() == 0x2ed {// call value is zero
			stackLemma(st,st.Operands());
			st := block_0_0x02ed(st); 
			return st;
		} 
		//|fp=0x0060|symbol|
		st := Push1(st,0x00);
		//|fp=0x0060|0x00,symbol|
		st := Dup(st,1);
		//|fp=0x0060|0x00,0x00,symbol|
		st := Revert(st); // revert if call value not zero
		return st;
	}

	method block_0_0x02ed(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02ed
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 1
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|symbol|
		st := JumpDest(st);
		//|fp=0x0060|symbol|
		st := Push2(st,0x02f5);
		//|fp=0x0060|0x2f5,symbol|
		st := Push2(st,0x0b30);
		//|fp=0x0060|0xb30,0x2f5,symbol|
		assume {:axiom} st.IsJumpDest(0xb30);
		st := Jump(st);
		//|fp=0x0060|0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0b30(st);
		return st;
	}

	method block_0_0x02f5(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02f5
	// Free memory pointer
	requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 
	requires st'.Read(0x60) == 0x04 && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 3
	// Static stack items
	requires st'.evm.stack.contents == [0x60,0x2f5,st'.Peek(2)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||*ptr(len),0x2f5,symbol|
		st := JumpDest(st);
		// ||*ptr(len),0x2f5,symbol|
		st := Push1(st,0x40);
		// ||0x40,*ptr(len),0x2f5,symbol|
		st := MLoad(st);
		// ||0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,1);
		// ||0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,1);
		// ||0xa0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Push1(st,0x20);
		// ||0x20,0xa0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,3);
		// ||0xa0,0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol| 
		stackLemma(st,st.Operands());
		st := block_0_0x02ff(st);  
		return st;
	}

	method block_0_0x02ff(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x02ff
	// Free memory pointer
	requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 
	requires st'.Read(0x60) == 0x04 && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [0xa0,0xc0,0xa0,0xa0,0x60,0x2f5,st'.Peek(6)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0xa0,0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol| 
		st := Dup(st,2);
		// ||0xc0,0xa0,0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|  
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		// ||0x20,0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|  
		st := Dup(st,3);
		// ||0xa0,0x20,0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol| 
		stackLemma(st,st.Operands());
		st := block_0_0x0302(st);
		return st;
	}

	method block_0_0x0302(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0302
	// Stack height(s)
	requires st'.Operands() == 8
	// Free memory pointer
	requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 
	requires st'.Read(0x60) == 0x04  && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Static stack items
	requires st'.evm.stack.contents == [0xa0,0x20,0xc0,0xa0,0xa0,0x60,0x2f5,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());	
		st := MStore(st);   
		// ||0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|  i.e. st.Read(0xa0) == 0x20
		//assert st.MemSize() >= 0xc0;// && st.Read(0xa0) == 0x20;
		stackLemma(st,st.Operands());
		st := block_0_0x0303(st);
		return st;
	}
		
	method block_0_0x0303(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0303
	// Stack height(s)
	requires st'.Operands() == 6
	// Free memory pointer
	requires st'.MemSize() >= 0xc0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20
	requires st'.Read(0x60) == 0x04  && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Static stack items
	requires st'.evm.stack.contents == [0xc0,0xa0,0xa0,0x60,0x2f5,st'.Peek(5)]
	{
		var st := st';
		stackLemma(st,st.Operands());	
		st := Dup(st,4);
		// ||*ptr(len),0xc0,0xa0,0xa0,*ptr(len)0x2f5,symbol| 
		st := Dup(st,2);
		// ||0xc0,*ptr(len),0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,2);
		// ||*ptr(len),0xc0,*ptr(len),0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := MLoad(st);
		// ||len,0xc0,*ptr(len),0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|   
		stackLemma(st,st.Operands());
		st := block_0_0x0307(st);
		return st;
	}

	method block_0_0x0307(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0307
	// Stack height(s)
	requires st'.Operands() == 9
	// Free memory pointer
	requires st'.MemSize() >= 0xc0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20
	requires st'.Read(0x60) == 0x04  && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Static stack items
	requires st'.evm.stack.contents == [st'.Read(0x60),0xc0,0x60,0xc0,0xa0,0xa0,0x60,0x2f5,st'.Peek(8)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||len,0xc0,*ptr(len),0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol| 
		st := Dup(st,2);
		// ||0xc0,len,0xc0,*ptr(len),0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := MStore(st);
		// ||0xc0,*ptr(len),0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol| i.e. st.MemSize() >= 0xe0 && st.Read(0xc0) == st.Read(0x60)
		st := Push1(st,0x20);
		// ||0x20,0xc0,*ptr(len),0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x030b(st);
		return st;
	}

	method block_0_0x030b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x030b
	// Stack height(s)
	requires st'.Operands() == 9
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x04
	requires st'.Read(0x60) == 0x04  && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Static stack items
	requires st'.evm.stack.contents == [0x20,0xc0,0x60,0xc0,0xa0,0xa0,0x60,0x2f5,st'.Peek(8)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0x20,0xc0,*ptr(len),0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0xe0,*ptr(len),0xc0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Swap(st,2);
		// ||0xc0,*ptr(len),0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// ||*ptr(len),0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,1);
		// ||*ptr(len),*ptr(len),0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := MLoad(st);
		// ||len,*ptr(len),0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0310(st);
		return st;
	}

	method block_0_0x0310(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0310
	// Stack height(s)
	requires st'.Operands() == 8
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x04
	requires st'.Read(0x60) == 0x04  && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Static stack items
	requires st'.evm.stack.contents == [0x04,0x60,0xe0,0xa0,0xa0,0x60,0x2f5,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||len,*ptr(len),0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Swap(st,1);
		// ||*ptr(len),len,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Push1(st,0x20);
		// |0x20,*ptr(len),len,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |0x80,len,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Swap(st,1);
		// |len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,1);
		// |len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,4);
		// |0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,4);
		// |0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Push1(st,0x00);
		// |0x0,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x031a(0,st); 
		return st;
	}

	// from 310: |0x0,0x80,0xe0,0x04,0x04,0x80,0xe0,0xa0,0xa0,0x60,0x2f5,symbol|
	// from 32d: |0x20*i,0x80,0xe0,0x04,0x04,0x80,0xe0,0xa0,0xa0,0x60,0x2f5,symbol|
	method block_0_0x031a(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x031a
	// Stack height(s)
	requires st'.Operands() == 12
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x04
	requires st'.Read(0x60) == 0x04 && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	requires i > 0 ==>  st'.MemSize() >= 0x100 && st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000 
	// Static stack items
	requires st'.Peek(0) as nat == i as nat * 0x20 <= 0x04 as nat + 0x1f
	requires st'.evm.stack.contents == [st'.Peek(0),0x80,0xe0,0x04,0x04,0x80,0xe0,0xa0,0xa0,0x60,0x2f5,st'.Peek(11)]
	// Termination
	decreases (st'.Read(0x60)+0x1f) - i*0x20,2
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		st := JumpDest(st);
		// |i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		st := Dup(st,4);
		// |len,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		st := Dup(st,2);
		// |i*0x20,len,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Lt(st);
		// |i*0x20<len,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := IsZero(st);
		// |i*0x20>=len,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol| i.e. for small string cond now true
		st := Push2(st,0x0335);
		// |0x335,i*0x20>=len,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assume {:axiom} st.IsJumpDest(0x335);
		st := JumpI(st);
		if st.PC() == 0x335 { 
			assert i == 1;
			// |i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
			stackLemma(st,st.Operands());
			st := block_0_0x0335(st); 
			return st;
		} 
		// i.e. first iteration, i == 0 < len
		// |0x0,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,1);
		// |0x0,0x0,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0324(i,st);
		return st;
	}

	method block_0_0x0324(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0324
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x04
	requires st'.Read(0x60) == 0x04 && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x0,0x80,0xe0,0x04,0x04,0x80,0xe0,0xa0,0xa0,0x60,0x2f5,st'.Peek(12)]
	requires i == 0
	decreases 0x04 - i,4
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |i*0x20,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,3);
		// |0x80,i*0x20,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |0x80+(i*0x20),i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0326(i,st);
		return st;
	}
	
	method block_0_0x0326(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0326
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 && st'.Read(0xa0) == 0x20 && st'.Read(0xc0) == 0x04
	requires st'.Read(0x60) == 0x04  && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 13
	// Static stack items
	requires st'.evm.stack.contents == [0x80,0x0,0x80,0xe0,0x04,0x04,0x80,0xe0,0xa0,0xa0,0x60,0x2f5,st'.Peek(12)]
	// Storage
	requires i == 0
	decreases 0x04 - i,3
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |0x80+(i*0x20),i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := MLoad(st);
		// |st.Read(0x80+(i*0x20)),i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		//assert st.Peek(0) == 0x5745544800000000000000000000000000000000000000000000000000000000;
		st := Dup(st,2);
		// |i,st.Read(0x80+(i*0x20)),i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
    	st := Dup(st,5);
		// |0xe0,i,st.Read(0x80+(i*0x20)),i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |0xe0+i,st.Read(0x80+(i*0x20)),i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x032a(i,st);
		return st;
	}

	method block_0_0x032a(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x032a
	// Free memory pointer
	requires st'.MemSize() >= 0xe0 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04  
									&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x04
	// Stack height(s)
	requires st'.Operands() == 14
	// Static stack items
	requires i == 0
	requires st'.evm.stack.contents == [0xe0,st'.Read(0x80),0x0,0x80,0xe0,0x04,0x04,0x80,0xe0,0xa0,0xa0,0x60,0x2f5,st'.Peek(13)]
	// Storage
	decreases 0x04 - i,2
	{
		var st := st';
		stackLemma(st,st.Operands());
		st := MStore(st);
		stackLemma(st,st.Operands());
		st := block_0_0x032b(i,st);
		return st;
	}

	method block_0_0x032b(i: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x032b
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04  
									&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
									&& st'.Read(0xa0) == 0x20 
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires i == 0
	requires st'.evm.stack.contents == [0x0,0x80,0xe0,0x04,0x04,0x80,0xe0,0xa0,0xa0,0x60,0x2f5,st'.Peek(11)]
	// Storage
	decreases 0x04 - i,1
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|  
		st := Push1(st,0x20);
		// |0x20,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		st := Dup(st,2);
		// |i,0x20,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |i+0x20,i*0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		st := Swap(st,1);
		// |i*0x20,(i*0x20)+0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		st := Pop(st);
		// |(i*0x20)+0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		st := Push2(st,0x031a);
		// |0x31a,(i*0x20)+0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		assume {:axiom} st.IsJumpDest(0x31a);
		st := Jump(st);
		// |(i*0x20)+0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symboll|
		stackLemma(st,st.Operands());
		st := block_0_0x031a(i+1,st);
		return st;
	}

	// from 031a ... i.e. i'+0x20<len and i' == 0
	// |i'+0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
	method block_0_0x0335(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0335
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 12
	// Static stack items
	requires st'.evm.stack.contents == [st'.Peek(0),st'.Peek(1),st'.Peek(2),st'.Peek(3),0x04,0x80,0xe0,0xa0,0xa0,0x60,0x2f5,st'.Peek(11)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := JumpDest(st);
		// |0x20,0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// |0x80,0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// |0xe0,len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// |len,len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// |len,0x80,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Swap(st,1);
		// |0x80,len,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// |len,0xe0,0xa0,0xa0,*ptr(len),0x2f5,symbo|
		st := Swap(st,1);
		// |0xe0,len,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x033d(st);
		return st;
	}

	method block_0_0x033d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x033d
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [0xe0,0x04,0xa0,0xa0,0x60,0x2f5,st'.Peek(6)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |0xe0,len,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,2);
		// |len,0xe0,len,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |len+0xe0==0xe4,len,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Swap(st,1);
		// |len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Push1(st,0x1f);
		// |0x1f,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := AndU5(st);
		// |len%32==len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,1);
		// |len,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := IsZero(st);
		// |len==0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Push2(st,0x0362);
		// //||0x0362,0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0348(st);
		return st;
	}

	method block_0_0x0348(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0348
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									//&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x362,0x0,0x04,0xe4,0xa0,0xa0,0x60,0x2f5,st'.Peek(8)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0x0362,0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assume {:axiom} st.IsJumpDest(0x362);
		st := JumpI(st);
		if st.PC() == 0x362 { 
			assert false; // Dead code i.e. (len % 32) == 0 and since whole words of output, no need for masking of last word of string output
			//||len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
			st := block_0_0x0362(st); 
			return st;
		}
		//||len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,1);
		//||len,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,3);
		//||0xe4,len,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		assert st.Peek(0) == 0xe0;
		//||0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,1);
		//||0xe0,0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := MLoad(st);
		//||Read(0xe0),0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Push1(st,0x01);
		//||0x01,Read(0xe0),0xe0,len,0xe4,0xa0,0xa0*ptr(len),0x2f5,symbol|
		st := Dup(st,4);
		//||len,0x01,Read(0xe0),0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0351(st);
		return st;
	}

	method block_0_0x0351(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0351
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									//&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x04,0x1,st'.Read(0xe0),0xe0,st'.Peek(4),st'.Peek(5),0xa0,0xa0,0x60,0x2f5,st'.Peek(10)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||len,0x01,Read(0xe0),0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Push1(st,0x20);
		//||0x20,len,0x01,Read(0xe0),0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//||0x1c,0x01,Read(0xe0),0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Push2(st,0x0100);
		//||0x100,0x1c,0x01,Read(0xe0),0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert (st.Peek(1) == 0x1c);
		st := Exp(st);
		//||(2^224),0x01,Read(0xe0),0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0358(st);
		return st;
	}
	
	method block_0_0x0358(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0358
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									//&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x100000000000000000000000000000000000000000000000000000000,0x1,st'.Read(0xe0),0xe0,st'.Peek(4),st'.Peek(5),0xa0,0xa0,0x60,0x2f5,st'.Peek(10)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||(2^224),0x01,Read(0xe0),0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert st.Peek(1) <= st.Peek(0);
		var temp := st.Peek(0) - st.Peek(1); 
		st := Sub(st);
		assert st.Peek(0) == temp;
		//||0xffffffffffffffffffffffffffffffffffffffffffffffffffffff,Read(0xe0),0xe0,len%32,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Not(st);
		stackLemma(st,st.Operands());
		st := block_0_0x035a(st);
		return st;
	}
		
	method block_0_0x035a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x035a
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									//&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 10
	// Static stack items
	requires st'.evm.stack.contents == [0xffffffff00000000000000000000000000000000000000000000000000000000,st'.Read(0xe0),0xe0,st'.Peek(3),st'.Peek(4),0xa0,0xa0,0x60,0x2f5,st'.Peek(9)]
	{
		var st := st';	
		stackLemma(st,st.Operands());
		assert st.Peek(1) % 0x100000000000000000000000000000000000000000000000000000000 == 0;
		st := AndUpper4Bytes(st);
		stackLemma(st,st.Operands());
		st := block_0_0x035b(st);
		return st;
	}

	method block_0_0x035b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x035b
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									//&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x5745544800000000000000000000000000000000000000000000000000000000,0xe0,st'.Peek(2),st'.Peek(3),0xa0,0xa0,0x60,0x2f5,st'.Peek(8)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0x5745544800000000000000000000000000000000000000000000000000000000,0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Dup(st,2);
		//||0xe0,0x5745544800000000000000000000000000000000000000000000000000000000,0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := MStore(st);
		//||0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol| i.e. st.Read(0xe0) is unchanged
		stackLemma(st,st.Operands());
		st := block_0_0x035d(st);
		return st;
	}
		
	method block_0_0x035d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x035d
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									//&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [0xe0,st'.Peek(1),st'.Peek(2),0xa0,0xa0,0x60,0x2f5,st'.Peek(7)]
	{
		var st := st';	
		stackLemma(st,st.Operands());
		//||0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol| 
		st := Push1(st,0x20);
		//||0x20,0xe0,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//||0x100,len,0xe4,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Swap(st,2);
		//||0xe4,len,0x100,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		//||len,0x100,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0362(st);
		return st;
	}

	method block_0_0x0362(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0362
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									//&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000 
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [st'.Peek(0),0x100,0xa0,0xa0,0x60,0x2f5,st'.Peek(6)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||len,0x100,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := JumpDest(st);
		//||len,0x100,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		//||0x100,0xa0,0xa0,*ptr(len),0x2f5,symbol|
		st := Swap(st,3);
		//||*ptr(len),0xa0,0xa0,0x100,0x2f5,symbol|
		st := Pop(st);
		//||0xa0,0xa0,0x100,0x2f5,symbol|
		st := Pop(st);
		//||0xa0,0x100,0x2f5,symbol|
		st := Pop(st);
		//||0x100,0x2f5,symbol|
		st := Push1(st,0x40);
		//||0x40,0x100,0x2f5,symbol|
		st := MLoad(st);
		//||0xa0,0x100,0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x036b(st);
		return st;
	}

	method block_0_0x036b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x036b
	// Free memory pointer
	requires st'.MemSize() >= 0x100 && st'.Read(0x40) == 0xa0 
									&& st'.Read(0x60) == 0x04 
									//&& st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000 
									&& st'.Read(0xa0) == 0x20
									&& st'.Read(0xc0) == 0x04
									&& st'.Read(0xe0) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires st'.evm.stack.contents == [0xa0,0x100,0x2f5,st'.Peek(3)]
	
	// ensures data := Memory.Slice(st.evm.memory, 0xa0, 0x60);
	// 0000000000000000000000000000000000000000000000000000000000000020 i.e. array starts at pos 32 (the 2nd word)
	// 0000000000000000000000000000000000000000000000000000000000000004 i.e. array size of 4 bytes
	// 5745544800000000000000000000000000000000000000000000000000000000 i.e. string == "WETH"
	{
		var st := st';
		stackLemma(st,st.Operands());
		//||0xa0,0x100,0x2f5,symbol|
		st := Dup(st,1);
		//||0xa0,0xa0,0xe4,0x2f5,symbol|
		st := Swap(st,2);
		//||0x100,0xa0,0xa0,0x2f5,symbol|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//||0x60,0xa0,0x2f5,symbol|
		st := Swap(st,1);
		//||0xa0,0x60,0x2f5,symbol|
		st := Return(st);
		return st;
	}

	method block_0_0x0b30(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b30
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 2
	// Static stack items
	requires st'.evm.stack.contents == [0x2f5,st'.Peek(1)]
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|0x2f5,symbol|
		st := JumpDest(st);
		//|fp=0x0060|0x2f5,symbol|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,0x2f5,symbol|
		st := Dup(st,1);
		//|fp=0x0060|0x01,0x01,0x2f5,symbol|
		st := SLoad(st);
		//|fp=0x0060|st.Load(0x01),0x01,0x2f5,symbol|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,st.Load(0x01),0x01,0x2f5,symbol|
		st := Dup(st,2);
		//|fp=0x0060|st.Load(0x01),0x01,st.Load(0x01),0x01,0x2f5,symbol|
		st := Push1(st,0x01);
		//|fp=0x0060|0x01,st.Load(0x01),0x01,st.Load(0x01),0x01,0x2f5,symbol|
		st := AndU1(st);
		//|fp=0x0060|0,0x01,st.Load(0x01),0x01,0x2f5,symbol| // i.e. first bit of Load(0x01) is 0
		stackLemma(st,st.Operands());
		st := block_0_0x0b3b(st);
		return st;
	}

	method block_0_0x0b3b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b3b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x01,st'.Load(0x01),0x01,0x2f5,st'.Peek(5)]
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|st.Load(0x01) is odd,0x01,st.Load(0x01),0x01,0x2f5,symbol| 
		st := IsZero(st);
		//|fp=0x0060|st.Load(0x01) is even,0x01,st.Load(0x01),0x01,0x2f5,symbol| 
		st := Push2(st,0x0100);
		//|fp=0x0060|0x0100,st.Load(0x01) is even,0x01,st.Load(0x01),0x01,0x2f5,symbol| 
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		//|fp=0x0060|0x0100,0x01,st.Load(0x01),0x01,0x2f5,symbol| 
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		//|fp=0x0060|0x0ff,st.Load(0x01),0x01,0x2f5,symbol| 
		// ==========================================================
		// NOTE: Reimplemented following to avoid need to reason about bitvector
		// arithmetic.
		// st := And(st);
		assert st.evm.stack.contents == [0x0ff,st.Load(0x01),0x01,0x2f5,st.Peek(4)];
		if st.Peek(0) == MAX_U256 as u256 { 
			// Masking against MAX_U256 (a nop)
			st := st.Pop().Next();
		} else {
			// Masking against 0xFF
			st := AndU8(st); // i.e. since short string get first byte of st.Load(0x01), i.e. len*2
			assert st.Peek(0) == st.Load(0x1) % 256 == 0x8;
		}    
		//|fp=0x0060|len*2,0x01,0x2f5,symbol| 
		st := Push1(st,0x02);
		//|fp=0x0060|0x02,len*2,0x01,0x2f5,symbol| 
		st := Swap(st,1);
		//|fp=0x0060|len*2,0x02,0x01,0x2f5,symbol|
		assert st.Peek(1) != 0;
		st := Div(st);
		//|fp=0x0060|len,0x01,0x2f5,symbol|
		stackLemma(st,st.Operands());
		//assert st.evm.stack.contents == [0x04,0x01,0x2f5,st.Peek(3)];
		st := block_0_0x0b46(st);
		return st;
	}

	method block_0_0x0b46(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b46
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 4
	// Static stack items
	requires st'.evm.stack.contents == [0x04,0x01,0x2f5,st'.Peek(3)]
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		//|fp=0x0060|len,0x01,0x2f5,symbol|
		st := Dup(st,1);
		//|fp=0x0060|len,len,0x01,0x2f5,symbol|
		st := Push1(st,0x1f);
		//|fp=0x0060|0x1f,len,len,0x01,0x2f5,symbol|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		//|fp=0x0060|len+0x1f==0x23,len,0x01,0x2f5,symbol|
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,l0x23,len,0x01,0x2f5,symbol|
		st := Dup(st,1);
		// |fp=0x0060|0x20,0x20,0x23,len,0x01,0x2f5,symbol|
		st := Swap(st,2);
		// |fp=0x0060|0x23,0x20,0x20,len,0x01,0x2f5,symbol|
		assert st.Peek(1) != 0;
		st := Div(st);
		// |fp=0x0060|0x01,0x20,len,0x01,0x2f5,symbol| // i.e. Peek(0) represents number of storage locations?
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		// |fp=0x0060|0x20,0x4,0x01,0x2f5,symbol|   
		stackLemma(st,st.Operands());
		st := block_0_0x0b50(st);
		return st;
	}

	method block_0_0x0b50(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b50
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 5
	// Static stack items
	requires st'.evm.stack.contents == [0x20,0x04,0x01,0x2f5,st'.Peek(4)]
	// Storage
  	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		// |fp=0x0060|0x20,len,0x01,0x2f5,symbol| 
		st := Push1(st,0x20);
		// |fp=0x0060|0x20,0x20,len,0x01,0x2f5,symbol| 
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |fp=0x0060|0x40,len,0x01,0x2f5,symbol| 
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0x40,len,0x01,0x2f5,symbol| 
		st := MLoad(st);
		// |fp=0x0060|mp==0x60,0x40,len,0x01,0x2f5,symbol|  i.e. Peek(0) == st'.Read(0x40) == fp
    	st := Swap(st,1);
		// |fp=0x0060|0x40,mp,len,0x01,0x2f5,symbol| 
		st := Dup(st,2);
		// |fp=0x0060|mp,0x40,mp,len,0x01,0x2f5,symbol|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// |fp=0x0060|mp+0x40==0xa0,mp,len,0x01,0x2f5,symbol|
		st := Push1(st,0x40);
		// |fp=0x0060|0x40,0xa0,mp,len,0x01,0x2f5,symbol|   
		stackLemma(st,st.Operands());
		st := block_0_0x0b5b(st);
		return st;
	}

	method block_0_0x0b5b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b5b
	// Free memory pointer
	requires st'.MemSize() >= 0x60 && st'.Read(0x40) == 0x60
	// Stack height(s)
	requires st'.Operands() == 7
	// Static stack items
	requires st'.evm.stack.contents == [0x40,0xa0,0x60,0x04,0x01,0x2f5,st'.Peek(6)]
	// Storage
	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
  	{
		var st := st';
		stackLemma(st,st.Operands());
		// |fp=0x0060|0x40,mp+0x40==0xa0,mp==0x60,len,0x01,0x2f5,symbol|   
		st := MStore(st);
		// |fp=0x0060|prev_mp==0x60,len,0x01,0x2f5,symbol|     // i.e. update st.Read(0x40) == 0xa0 
    	st := Dup(st,1);
		// |fp=0x0060|0x60,0x60,len,0x01,0x2f5,symbol|
		st := Swap(st,3);
		// |fp=0x0060|0x01,0x60,len,0x60,0x2f5,symbol|
		st := Swap(st,2);
		// |fp=0x0060|len,0x60,0x01,0x60,0x2f5,symbol|
		st := Swap(st,1);
		// ||0x60,len,0x01,0x60,0x2f5,symbol|
		st := Dup(st,2);
		// ||len,0x60,len,0x01,0x60,0x2f5,symbol|
		st := Dup(st,2);
		// ||0x60,len,0x60,len,0x01,0x60,0x2f5,symbol|
		st := MStore(st);
		// ||*ptr(len),len,0x01,*ptr(len),0x2f5,symbol| i.e st.Read(0x60) == len
		stackLemma(st,st.Operands());
		st := block_0_0x0b63(st);
		return st;
	}

	method block_0_0x0b63(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b63
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x04 // i.e len
	// Stack height(s)
	requires st'.Operands() == 6
	// Static stack items
	requires st'.evm.stack.contents == [0x60,0x04,0x01,0x60,0x2f5,st'.Peek(5)]
	// Storage
	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||*ptr(len),len,0x01,*ptr(len),0x2f5,symbol| 
		st := Push1(st,0x20);
		// ||0x20,*ptr(len),len,0x01,*ptr(len),0x2f5,symbol| 
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := Dup(st,3);
		// ||0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := Dup(st,1);
		// ||0x01,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := SLoad(st);
		// ||st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := Push1(st,0x01);
		// ||0x01,st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := Dup(st,2);
		// ||st.Load(0x1),0x01,st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := Push1(st,0x01);
		// ||0x01,st.Load(0x1),0x01,st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0b6e(st);
		return st;
	}

	method block_0_0x0b6e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b6e
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x04          
	// Stack height(s)
	requires st'.Operands() == 11
	// Static stack items
	requires st'.evm.stack.contents == [0x01,st'.Load(0x1),0x01,st'.Load(0x1),0x01,0x80,0x04,0x01,0x60,0x2f5,st'.Peek(10)]
	// Storage
	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0x01,st.Load(0x1),0x01,st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := AndU1(st);
		// ||0x0,0x01,st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := IsZero(st);
		// ||0x1,0x01,st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| i.e. true it is a short string
		st := Push2(st,0x0100);
		// ||0x100,0x1,0x01,st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		// ||0x100,0x01,st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		assert st.Peek(1) <= st.Peek(0);
		st := Sub(st);
		// ||0xff,st.Load(0x1),0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		//assert st.Peek(0) in {MAX_U256 as u256, 0xFF};
		// ==========================================================
		// NOTE: Reimplemented following to avoid need to reason about bitvector
		// arithmetic.
		// st := And(st);
		if st.Peek(0) == MAX_U256 as u256 { 
			// Masking against MAX_U256 (a nop)
			st := st.Pop().Next();
		} else {
			// Masking against 0xFF
			st := AndU8(st);
			assert (st.Peek(0) == 0x08);
		}
		// ==========================================================
    	
		// ||len*2,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := Push1(st,0x02);
		// ||0x02,len*2,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := Swap(st,1);
		// ||len*2,0x02,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		stackLemma(st,st.Operands());
		st := block_0_0x0b79(st);
		return st;
	}

	method block_0_0x0b79(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b79
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x04     
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x08,0x02,0x01,0x80,0x04,0x01,0x60,0x2f5,st'.Peek(8)]
	// Storage
	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||len*2,0x02,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		assert st.Peek(1) != 0;
		st := Div(st);
		// ||len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := Dup(st,1);
		// ||len,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := IsZero(st);
		// ||0,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := Push2(st,0x0bc6);
		// ||0xbc6,0,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		assume {:axiom} st.IsJumpDest(0xbc6);
		st := JumpI(st);
		if st.PC() == 0xbc6 { // dead code i.e. this path is for when len == 0
			assert false;
			// ||len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
			stackLemma(st,st.Operands());
			st := block_0_0x0bc6(st); 
			return st;
		} 
		// ||len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := Dup(st,1);
		// ||len,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := Push1(st,0x1f);
		// ||0x1f,len,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := Lt(st);
		// ||0x1f<len==0,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|   
		stackLemma(st,st.Operands());
		st := block_0_0x0b84(st);
		return st;
	}

	method block_0_0x0b84(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b84
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x04      
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x0,0x04,0x01,0x80,0x04,0x01,0x60,0x2f5,st'.Peek(8)]
	// Storage
 	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||0,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|    
		st := Push2(st,0x0b9b);
		// ||0xb9b,0,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|   
		assume {:axiom} st.IsJumpDest(0xb9b);
		st := JumpI(st);
		if st.PC() == 0xb9b { // this path is impossible
			// ||len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| where len > 0x1f
			//
			// Deadcode begins here.  The reason is that the following code is used
			// to account for copying strings whose length exceeds 31 bytes.
			// However, the actual length of the string involved in this case
			// ("WETH") is only 4 bytes.
      		assert false;
      		//st := block_0_0x0b9b(st); 
			//return st;
    	}
		// ||len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := Push2(st,0x0100);
		// ||0x100,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := Dup(st,1);
		// ||0x100,0x100,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| 
		st := Dup(st,4);
		// ||0x01,0x100,0x100,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := SLoad(st);
		// ||st.Load(0x1),0x100,0x100,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		assert st.Peek(1) != 0;
		st := Div(st);
		// ||st.Load(0x1)>>8,0x100,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
		st := Mul(st);
		// ||(st.Load(0x1)>>8)<<8,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0b90(st);
		return st;
	}

	method block_0_0x0b90(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0b90
	// Free memory pointer
	requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && st'.Read(0x60) == 0x04      
	// Stack height(s)
	requires st'.Operands() == 9
	// Static stack items
	requires st'.evm.stack.contents == [0x5745544800000000000000000000000000000000000000000000000000000000,0x04,0x01,0x80,0x04,0x01,0x60,0x2f5,st'.Peek(8)]
	// Storage
	requires st'.Load(0x01) == 0x5745544800000000000000000000000000000000000000000000000000000008 // "WETH" ... 0s ... len*2  
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||(st.Load(0x1)>>8)<<8,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := Dup(st,4);
		// ||0x80,(st.Load(0x1)>>8)<<8,len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|
		st := MStore(st);
		// ||len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol| i.e st.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
		st := Swap(st,2);
		// ||0x80,0x01,len,len,0x01,*ptr(len),0x2f5,symbol|
		st := Push1(st,0x20);
		// ||0x20,0x80,0x01,len,len,0x01,*ptr(len),0x2f5,symbol|
		assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
		st := Add(st);
		// ||0xa0,0x01,len,len,0x01,*ptr(len),0x2f5,symbol|
		st := Swap(st,2);
		// ||len,0x01,0xa0,len,0x01,*ptr(len),0x2f5,symbol|
		st := Push2(st,0x0bc6);
		// ||0xbc6,len,0x01,0xa0,len,0x01,*ptr(len),0x2f5,symbol|
		assume {:axiom} st.IsJumpDest(0xbc6);
		st := Jump(st);
		// ||len,0x01,0xa0,len,0x01,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x0bc6(st);
		return st;
	}

	// this path is impossible i.e requires len > 0x1f, where as here len == 4
	// method block_0_0x0b9b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0b9b
	// // Free memory pointer
	// requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && 0x1f < st'.Read(0x60) < 0xff
	// // Stack height(s)
	// requires st'.Operands() == 8
	// {
	// 	var st := st';
	// 	st := JumpDest(st);
	// 	st := Dup(st,3);
	// 	assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
	// 	st := Add(st);
	// 	var n := st.Peek(0); // n == len + 0x80 and note that 0x9f < n < 0x17f
	// 	st := Swap(st,2);
	// 	st := Swap(st,1);
	// 	st := Push1(st,0x00);
	// 	st := MStore(st);
	// 	st := Push1(st,0x20);
    // 	st := block_0_0x0ba5(n,st); 
	// 	return st;
	// }

	// method block_0_0x0ba5(n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0ba5
	// // Free memory pointer
	// requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && 0x1f < st'.Read(0x60) < 0xff && st'.Read(0x0) == 0x1 
	// // Stack height(s)
	// requires st'.Operands() == 8
	// {
	// 	var st := st';
	// 	st := Push1(st,0x00);
	// 	st := Keccak256(st);
	// 	st := Swap(st,1);
	// 	st := block_0_0x0ba9(0x80,n,st);
	// 	return st;
	// }

	// method block_0_0x0ba9(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0ba9
	// // Free memory pointer
	// requires st'.MemSize() >= 0x80 && st'.Read(0x40) == 0xa0 && 0x1f < st'.Read(0x60) < 0xff 
	// // Stack height(s)
	// requires st'.Operands() == 8
	// {
	// 	var st := st';
	// 	st := JumpDest(st);
	// 	st := Dup(st,2);
	// 	st := SLoad(st);
	// 	st := Dup(st,2);
	// 	st := MStore(st);	
	// 	st := Swap(st,1);
	// 	st := Push1(st,0x01);
	// 	st := Add(st);
	// 	st := block_0_0x0bb2(i,n,st);
	// 	return st;
	// }

	// method block_0_0x0bb2(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0bb2
	// // Free memory pointer
	// requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 && 0x1f < st'.Read(0x60) < 0xff  //&& st'.Read(0x0) == 0x1 && st'.Read(0x80) == st'.Load(Hash(0x1))
	// // Stack height(s)
	// requires st'.Operands() == 8
	// {
	// 	var st := st';
	// 	st := Swap(st,1);
	// 	st := Push1(st,0x20);
	// 	assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
	// 	st := Add(st);
	// 	st := Dup(st,1);
	// 	st := Dup(st,4);
	// 	st := Gt(st);
	// 	st := block_0_0x0bb9(i+0x20,n,st);
	// 	return st;
	// }

	// method block_0_0x0bb9(i: u256, n: u256, st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0bb9
	// // Free memory pointer
	// requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 && 0x1f < st'.Read(0x60) < 0xff  //&& st'.Read(0x0) == 0x1 && st'.Read(0x80) == st'.Load(Hash(0x1))
	// // Stack height(s)
	// requires st'.Operands() == 9
	// {
	// 	var st := st';
	// 	st := Push2(st,0x0ba9);
	// 	assume {:axiom} st.IsJumpDest(0xba9);
	// 	st := JumpI(st);
	// 	if st.PC() == 0xba9 { 
	// 		// n > i
	// 		st := block_0_0x0ba9(i,n,st); 
	// 		return st;
	// 	}
	// 	// n <= i
	// 	st := Dup(st,3);
	// 	st := Swap(st,1);
	// 	assert st.Peek(1) <= st.Peek(0);
	// 	st := Sub(st);
	// 	st := Push1(st,0x1f);
	// 	st := AndU5(st);
	// 	st := Dup(st,3);
	// 	st := block_0_0x0bc4(st);
	// 	return st;
	// }

	// method block_0_0x0bc4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	// requires st'.evm.code == Code.Create(BYTECODE_0)
	// requires st'.WritesPermitted() && st'.PC() == 0x0bc4
	// // Free memory pointer
	// requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 && 0x1f < st'.Read(0x60) < 0xff 
	// 								// && st'.Read(0x80) == st'.Load(Hash(0x1)) ...&& st'.Read(0xa0) == st'.Load(Hash(0x1)+1) ... etc
	// // Stack height(s)
	// requires st'.Operands() == 9
	// // Storage
	// //requires (st'.Read(0x60) <= 0xffff)  
	// {
	// 	var st := st';
	// 	assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
	// 	st := Add(st);
	// 	st := Swap(st,2);
	// 	st := block_0_0x0bc6(st);
	// 	return st;
	// }

	// from b79 (dead path):	||len,0x01,0x80,len,0x01,*ptr(len),0x2f5,symbol|  i.e. len == 0
	// from b90:				||len,0x01,0xa0,len,0x01,*ptr(len),0x2f5,symbol|  i.e. len <= 0x1f
	// from bc4 (dead Path): 	||Hash(0x1)+k,i,n,len,0x01,*ptr(len),0x2f5,symbol|  i.e. len > 0x1f
	method block_0_0x0bc6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
	requires st'.evm.code == Code.Create(BYTECODE_0)
	requires st'.WritesPermitted() && st'.PC() == 0x0bc6
	// Free memory pointer
	requires st'.MemSize() >= 0xa0 && st'.Read(0x40) == 0xa0 
	requires st'.Read(0x60) == 0x04  && st'.Read(0x80) == 0x5745544800000000000000000000000000000000000000000000000000000000
	// Stack height(s)
	requires st'.Operands() == 8
	// Static stack items
	requires st'.evm.stack.contents == [st'.Peek(0),st'.Peek(1),st'.Peek(2),st'.Peek(3),st'.Peek(4),0x60,0x2f5,st'.Peek(7)]
	{
		var st := st';
		stackLemma(st,st.Operands());
		// ||len,0x01,0xa0,len,0x01,*ptr(len),0x2f5,symbol|
		st := JumpDest(st);
		// ||len,0x01,0xa0,len,0x01,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// ||0x01,0xa0,len,0x01,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// ||0xa0,len,0x01,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// ||len,0x01,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// ||0x01,*ptr(len),0x2f5,symbol|
		st := Pop(st);
		// ||*ptr(len),0x2f5,symbol|
		st := Dup(st,2);
		// ||0x2f5,*ptr(len),0x2f5,symbol|
		assume {:axiom} st.IsJumpDest(0x2f5);
		st := Jump(st);
		// ||0x2f5,*ptr(len),0x2f5,symbol|
		stackLemma(st,st.Operands());
		st := block_0_0x02f5(st);
		return st;
	}

}
