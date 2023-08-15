include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module Decimals {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // decimals()
    // ============================================================================

    method block_0_0x0260(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0260
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x026b);
        assume st.IsJumpDest(0x26b);
        st := JumpI(st);
        if st.PC() == 0x26b { st := block_0_0x026b(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method block_0_0x026b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x026b
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x0273);
        st := Push2(st,0x0aff);
        assume st.IsJumpDest(0xaff);
        st := Jump(st);
        st := block_0_0x0aff(st);
        return st;
    }

    method {:verify false} block_0_0x0aff(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0aff
    requires st'.Operands() == 2
    requires (st'.Peek(0) == 0x273)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x02);
        st := Push1(st,0x00);
        st := Swap(st,1);
        st := SLoad(st);
        st := Swap(st,1);
        st := Push2(st,0x0100);
        st := Exp(st);
        st := Swap(st,1);
        st := Div(st);
        st := Push1(st,0xff);
        st := And(st);
        st := Dup(st,2);
        assume st.IsJumpDest(0x273);
        st := Jump(st);
        st := block_0_0x0273(st);
        return st;
    }

    method {:verify false} block_0_0x0273(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0273
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x273)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Dup(st,1);
        st := Dup(st,3);
        st := Push1(st,0xff);
        st := And(st);
        st := Push1(st,0xff);
        st := And(st);
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