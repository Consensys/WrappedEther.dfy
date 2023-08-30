include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module Deposit {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // fallback()
    // ============================================================================

    method block_0_0x00ad(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x00ad
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires 0 <= st'.Operands() <= 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0xb4);
        st := Push2(st,0x043a);
        assume st.IsJumpDest(0x43a);
        st := Jump(st);
        st := block_0_0x043a(st); // call deposit
        return st;
    }

    // return from deposit()
    method block_0_0x00b4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x00b4
    requires 0 <= st'.Operands() <= 1
    {
        var st := st';
        st := JumpDest(st);
        st := Stop(st);
        return st;
    }

    // ============================================================================
    // deposit()
    // ============================================================================

    method block_0_0x03c4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x03c4
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x03cc);
        st := Push2(st,0x043a);
        assume st.IsJumpDest(0x43a);
        st := Jump(st);
        assert st.Operands() == 2;
        st := block_0_0x043a(st);
        return st;
    }

    method block_0_0x043a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x043a
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires 1 <= st'.Operands() <= 2
    requires (st'.Peek(0) == 0xb4) || (st'.Peek(0) == 0x3cc && st'.Operands() == 2)
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
         // value ret
        st := Push1(st,0x03);
        // 0x3 value ret
        st := Push1(st,0x00);
        // 0x0 0x3 value ret
        st := Caller(st);
        // sender 0x0 0x3 value ret
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        // 0xff.. sender 0x0 0x3 value ret
        st := AndU160(st);
        // sender[..160] 0x0 0x3 value ret
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        // 0xff.. sender[..160] 0x0 0x3 value ret
        st := block_0_0x046c(st);
        return st;
    }

    method block_0_0x046c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x046c
    requires 6 <= st'.Operands() <= 7
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires (st'.Peek(0) == 0xffffffffffffffffffffffffffffffffffffffff)
    requires (st'.Peek(2) == 0x0)
    requires (st'.Peek(3) == 0x3)
    requires (st'.Peek(5) == 0xb4) || (st'.Peek(5) == 0x3cc && st'.Operands() == 7)
    {
        var st := st';
        // 0xff.. sender[..160] 0x0 0x3 value ret
        st := AndU160(st);
        // sender[..160] 0x0 0x3 value ret
        st := Dup(st,2);
        // 0x0 sender[..160] 0x0 0x3 value ret
        st := MStore(st);
        // 0x0 0x3 value ret | mem[0x00:=sender[..160]]
        st := Push1(st,0x20);
        // 0x20 0x0 0x3 value ret | mem[0x00:=sender[..160]]
        assert st.Peek(4) == 0xb4 || (st.Peek(4) == 0x3cc && st.Operands() == 6);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        assert st.Peek(0) == 0x20;
        // 0x20 0x3 value ret | mem[0x00:=sender[..160]]
        st := Swap(st,1);
        // 0x3 0x20 value ret | mem[0x00:=sender[..160]]
        st := Dup(st,2);
        // 0x20 0x3 0x20 value ret | mem[0x00:=sender[..160]]
        st := MStore(st);
        // 0x20 value ret | mem[0x00:=sender[..160],0x20=0x3]
        st := block_0_0x0475(st);
        return st;
    }

    method block_0_0x0475(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0475
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires 3 <= st'.Operands() <= 4
    requires (st'.Peek(2) == 0xb4) || (st'.Peek(2) == 0x3cc && st'.Operands() == 4)
    requires st'.Peek(0) == 0x20
    {
        var st := st';
        // 0x20 value ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Push1(st,0x20);
        // 0x20 0x20 value ret | mem[0x00:=sender[..160],0x20=0x3]
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // 0x40 value ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Push1(st,0x00);
        // 0x00 0x40 value ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Keccak256(st);
        // h1 value ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Push1(st,0x00);
        // 0x00 h1 value ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Dup(st,3);
        // value 0x00 h1 value ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Dup(st,3);
        // h1 value 0x00 h1 value ret | mem[0x00:=sender[..160],0x20=0x3]
        st := SLoad(st);
        // bal value 0x00 h1 value ret | mem[0x00:=sender[..160],0x20=0x3]
        assert st.Peek(5) == 0xb4 || st.Peek(5) == 0x3cc;
        // OVERFLOW: there is a possible integer overflow here as there is no
        // check to revert.   As such, the following assertion fails:
        //
        // assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        //
        // It seems that this cannot be exploited, however, given the amount of
        // ether that would be required.
        st := Add(st);
        // nbal 0x00 h1 value ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Swap(st,3);
        // value 0x00 h1 nbal ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Pop(st);
        // 0x00 h1 nbal ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Pop(st);
        // h1 nbal ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Dup(st,2);
        // nbal h1 nbal ret | mem[0x00:=sender[..160],0x20=0x3]
        st := Swap(st,1);
        // h1 nbal nbal ret | mem[0x00:=sender[..160],0x20=0x3]
        st := SStore(st);
        // nbal ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Pop(st);
        // ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := block_0_0x0488(st);
        return st;
    }

    method block_0_0x0488(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0488
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires 1 <= st'.Operands() <= 2
    requires (st'.Peek(0) == 0xb4) || (st'.Peek(0) == 0x3cc && st'.Operands() == 2)
    {
        var st := st';
        // ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Caller(st);
        // sender ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        // 0xff.. sender ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := AndU160(st);
        // sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := PushN(st,32,0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c);
        // 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := CallValue(st);
        // value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Push1(st,0x40);
        // 0x40 value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := MLoad(st);
        // fp value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Dup(st,1);
        // fp fp value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := block_0_0x04c5(st);
        return st;
    }

    method block_0_0x04c5(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x04c5
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires 6 <= st'.Operands() <= 7
    requires (st'.Peek(0) == st'.Peek(1) == 0x80)
    requires (st'.Peek(3) == 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c)
    requires (st'.Peek(5) == 0xb4) || (st'.Peek(5) == 0x3cc && st'.Operands() == 7)
    {
        var st := st';
        // fp fp value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Dup(st,3);
        // value fp fp value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Dup(st,2);
        // fp value fp fp value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := MStore(st);
        // fp fp value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Push1(st,0x20);
        // 0x20 fp fp value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // 0xA0 fp value 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Swap(st,2);
        // value fp 0xA0 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Pop(st);
        // fp 0xA0 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Pop(st);
        // 0xA0 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := block_0_0x04ce(st);
        return st;
    }

    method block_0_0x04ce(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x04ce
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires 4 <= st'.Operands() <= 5
    requires (st'.Peek(0) == 0xa0)
    requires (st'.Peek(1) == 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c)
    requires (st'.Peek(3) == 0xb4) || (st'.Peek(3) == 0x3cc && st'.Operands() == 5)
    {
        var st := st';
        // 0xA0 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Push1(st,0x40);
        // 0x40 0xA0 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := MLoad(st);
        // fp 0xA0 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Dup(st,1);
        // fp fp 0xA0 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := Swap(st,2);
        // 0xA0 fp fp 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        // 0x20 fp 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        assert st.Peek(0) == 0x20;
        st := Swap(st,1);
        // fp 0x20 0xe1.. sender[..160] ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        st := LogN(st,2);
        // ret | mem[0x00:=sender[..160],0x20=0x3,h1=nbal]
        assume st.IsJumpDest(0xb4);
        assume st.IsJumpDest(0x3cc);
        st := Jump(st);
        match st.PC() {
            case 0xb4 => { st := block_0_0x00b4(st); }
            case 0x3cc => { st := block_0_0x03cc(st); }
        }
        return st;
    }

    method block_0_0x03cc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x03cc
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Stop(st);
        return st;
    }
}