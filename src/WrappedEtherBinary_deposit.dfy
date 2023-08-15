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
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x03cc);
        st := Push2(st,0x043a);
        assume st.IsJumpDest(0x43a);
        st := Jump(st);
        st := block_0_0x043a(st);
        return st;
    }

    method {:verify false} block_0_0x043a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x043a
    requires 1 <= st'.Operands() <= 2
    requires (st'.Peek(0) == 0xb4) || (st'.Peek(0) == 0x3cc) || (st'.Peek(0) == 0xb4)
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := Push1(st,0x03);
        st := Push1(st,0x00);
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := Dup(st,2);
        st := MStore(st);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Dup(st,2);
        st := MStore(st);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Push1(st,0x00);
        st := Keccak256(st);
        st := Push1(st,0x00);
        st := Dup(st,3);
        st := Dup(st,3);
        st := SLoad(st);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,3);
        st := Pop(st);
        st := Pop(st);
        st := Dup(st,2);
        st := Swap(st,1);
        st := SStore(st);
        st := Pop(st);
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := PushN(st,32,0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c);
        st := CallValue(st);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Dup(st,1);
        st := Dup(st,3);
        st := Dup(st,2);
        st := MStore(st);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,2);
        st := Pop(st);
        st := Pop(st);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Dup(st,1);
        st := Swap(st,2);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := Swap(st,1);
        st := LogN(st,2);
        assume st.IsJumpDest(0xb4);
        assume st.IsJumpDest(0x3cc);
        assume st.IsJumpDest(0xb4);
        st := Jump(st);
        match st.PC() {
            case 0xb4 => { st := block_0_0x00b4(st); } // => fallback()
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