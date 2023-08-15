include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module Allowance {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // allowance(address,address)
    // ============================================================================

    method block_0_0x03ce(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x03ce
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x03d9);
        assume st.IsJumpDest(0x3d9);
        st := JumpI(st);
        if st.PC() == 0x3d9 { st := block_0_0x03d9(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method {:verify false} block_0_0x03d9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x03d9
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x0424);
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
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := Swap(st,1);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Swap(st,2);
        st := Swap(st,1);
        st := Pop(st);
        st := Pop(st);
        st := Push2(st,0x0bdd);
        assume st.IsJumpDest(0xbdd);
        st := Jump(st);
        st := block_0_0x0bdd(st);
        return st;
    }

    method {:verify false} block_0_0x0bdd(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0bdd
    requires st'.Operands() == 4
    requires (st'.Peek(2) == 0x424)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x04);
        st := Push1(st,0x20);
        st := MStore(st);
        st := Dup(st,2);
        st := Push1(st,0x00);
        st := MStore(st);
        st := Push1(st,0x40);
        st := Push1(st,0x00);
        st := Keccak256(st);
        st := Push1(st,0x20);
        st := MStore(st);
        st := Dup(st,1);
        st := Push1(st,0x00);
        st := MStore(st);
        st := Push1(st,0x40);
        st := Push1(st,0x00);
        st := Keccak256(st);
        st := Push1(st,0x00);
        st := Swap(st,2);
        st := Pop(st);
        st := Swap(st,2);
        st := Pop(st);
        st := Pop(st);
        st := SLoad(st);
        st := Dup(st,2);
        assume st.IsJumpDest(0x424);
        st := Jump(st);
        st := block_0_0x0424(st);
        return st;
    }

    method {:verify false} block_0_0x0424(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0424
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x424)
    {
        var st := st';
        st := JumpDest(st);
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
        st := Return(st);
        return st;
    }
}