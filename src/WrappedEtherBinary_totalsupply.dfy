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
    //
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
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
    //
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
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

    method block_0_0x0667(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0667
    requires st'.Operands() == 2
    requires (st'.Peek(0) == 0x1ae)
    //
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
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

    // This block sets up a return frame by writing the value on top the stack
    // on entry into the first word of free memory.  This sequence is
    // surprisingly inefficient.
    method block_0_0x01ae(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x01ae
    requires st'.Operands() == 2
    //
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
    {
        ghost var val := st'.Peek(0);
        ghost var fp := st'.Read(0x40);
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x40);
        // 0x40 val
        st := MLoad(st);
        // fp val
        st := Dup(st,1);
        // fp fp val
        st := Dup(st,3);
        // val fp fp val
        st := Dup(st,2);
        // fp val fp fp val
        st := MStore(st);
        // fp fp val | mem[fp] = val
        st := Push1(st,0x20);
        // 0x20 fp fp val | mem[fp] = val
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // (fp+0x20) fp val | mem[fp] = val
        st := Swap(st,2);
        // val fp (fp+0x20) | mem[fp] = val
        st := Pop(st);
        // fp (fp+0x20) | mem[fp] = val
        st := Pop(st);
        // (fp+0x20) | mem[fp] = val
        st := Push1(st,0x40);
        // 0x40 (fp+0x20) | mem[fp] = val
        st := MLoad(st);
        // fp (fp+0x20) | mem[fp] = val
        st := Dup(st,1);
        // fp fp (fp+0x20) | mem[fp] = val
        st := Swap(st,2);
        // (fp+0x20) fp fp | mem[fp] = val
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        // 0x20 fp | mem[fp] = val
        st := Swap(st,1);
        // fp 0x20 | mem[fp] = val
        st := Return(st);
        return st;
    }
}