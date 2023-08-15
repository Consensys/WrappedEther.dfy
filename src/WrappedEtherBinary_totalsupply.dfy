include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module TotalSupply {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // totalSupply()
    // ============================================================================

    method block_0_0x019b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x019b
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x01a6);
        assume st.IsJumpDest(0x1a6);
        st := JumpI(st);
        if st.PC() == 0x1a6 { st := block_0_0x01a6(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method block_0_0x01a6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x01a6
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x01ae);
        st := Push2(st,0x0667);
        assume st.IsJumpDest(0x667);
        st := Jump(st);
        st := block_0_0x0667(st);
        return st;
    }

    method block_0_0x0667(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0667
    requires st'.Operands() == 2
    requires (st'.Peek(0) == 0x1ae)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x00);
        st := Address(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := Balance(st);
        st := Swap(st,1);
        st := Pop(st);
        st := Swap(st,1);
        assume st.IsJumpDest(0x1ae);
        st := Jump(st);
        st := block_0_0x01ae(st);
        return st;
    }

    method {:verify false} block_0_0x01ae(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x01ae
    requires st'.Operands() == 2
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