include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module Approve {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // approve(address,uin256)
    // ============================================================================

    method block_0_0x0141(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0141
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x014c);
        assume st.IsJumpDest(0x14c);
        st := JumpI(st);
        if st.PC() == 0x14c { st := block_0_0x014c(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method {:verify false} block_0_0x014c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x014c
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x0181);
        st := Push1(st,0x04);
        st := Dup(st,1);
        st := Dup(st,1);
        st := CallDataLoad(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := Swap(st,1);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Swap(st,2);
        st := Swap(st,1);
        st := Dup(st,1);
        st := CallDataLoad(st);
        st := Swap(st,1);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Swap(st,2);
        st := Swap(st,1);
        st := Pop(st);
        st := Pop(st);
        st := Push2(st,0x0575);
        assume st.IsJumpDest(0x575);
        st := Jump(st);
        st := block_0_0x0575(st);
        return st;
    }

    method {:verify false} block_0_0x0575(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0575
    requires st'.Operands() == 4
    requires (st'.Peek(2) == 0x181)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x00);
        st := Dup(st,2);
        st := Push1(st,0x04);
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
        st := Dup(st,6);
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
        st := Dup(st,2);
        st := Swap(st,1);
        st := SStore(st);
        st := Pop(st);
        st := Dup(st,3);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := PushN(st,32,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
        st := Dup(st,5);
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
        st := LogN(st,3);
        st := Push1(st,0x01);
        st := Swap(st,1);
        st := Pop(st);
        st := Swap(st,3);
        st := Swap(st,2);
        st := Pop(st);
        st := Pop(st);
        assume st.IsJumpDest(0x181);
        st := Jump(st);
        st := block_0_0x0181(st);
        return st;
    }

    method {:verify false} block_0_0x0181(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0181
    requires st'.Operands() == 2
    requires (st'.Peek(0) == 0x1)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Dup(st,1);
        st := Dup(st,3);
        st := IsZero(st);
        st := IsZero(st);
        st := IsZero(st);
        st := IsZero(st);
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
        st := Return(st);
        return st;
    }
}