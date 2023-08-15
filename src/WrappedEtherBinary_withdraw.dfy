include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module Withdraw {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // withdraw(uint256)
    // ============================================================================

    method block_0_0x023d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x023d
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x0248);
        assume st.IsJumpDest(0x248);
        st := JumpI(st);
        if st.PC() == 0x248 { st := block_0_0x0248(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method {:verify false} block_0_0x0248(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0248
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x025e);
        st := Push1(st,0x04);
        st := Dup(st,1);
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
        st := Push2(st,0x09d3);
        assume st.IsJumpDest(0x9d3);
        st := Jump(st);
        st := block_0_0x09d3(st);
        return st;
    }

    method {:verify false} block_0_0x09d3(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x09d3
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x25e)
    {
        var st := st';
        st := JumpDest(st);
        st := Dup(st,1);
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
        st := SLoad(st);
        st := Lt(st);
        st := IsZero(st);
        st := IsZero(st);
        st := IsZero(st);
        st := Push2(st,0x0a21);
        assume st.IsJumpDest(0xa21);
        st := JumpI(st);
        if st.PC() == 0xa21 { st := block_0_0x0a21(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method {:verify false} block_0_0x0a21(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0a21
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x25e)
    {
        var st := st';
        st := JumpDest(st);
        st := Dup(st,1);
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
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
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
        st := Push2(st,0x08fc);
        st := Dup(st,3);
        st := Swap(st,1);
        st := Dup(st,2);
        st := IsZero(st);
        assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
        st := Mul(st);
        st := Swap(st,1);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Push1(st,0x00);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Dup(st,1);
        st := Dup(st,4);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := Dup(st,2);
        st := Dup(st,6);
        st := Dup(st,9);
        st := Dup(st,9);
        var CONTINUING(cc) := Call(st);
        {
            var inner := cc.CallEnter(1);
            if inner.EXECUTING? { inner := external_call(cc.sender,inner); }
            st := cc.CallReturn(inner);
        }
        st := Swap(st,4);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := IsZero(st);
        st := IsZero(st);
        st := Push2(st,0x0aae);
        assume st.IsJumpDest(0xaae);
        st := JumpI(st);
        if st.PC() == 0xaae { st := block_0_0x0aae(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method {:verify false} block_0_0x0aae(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0aae
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x25e)
    {
        var st := st';
        st := JumpDest(st);
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := PushN(st,32,0x7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65);
        st := Dup(st,3);
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
        st := Pop(st);
        assume st.IsJumpDest(0x25e);
        st := Jump(st);
        st := block_0_0x025e(st);
        return st;
    }

    method block_0_0x025e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x025e
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Stop(st);
        return st;
    }
}