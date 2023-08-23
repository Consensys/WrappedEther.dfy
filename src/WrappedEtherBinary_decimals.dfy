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

    method block_0_0x0260(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0260
    requires st'.Operands() == 1
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
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

    method block_0_0x026b(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x026b
    requires st'.Operands() == 1
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
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

    method block_0_0x0aff(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0aff
    requires st'.Operands() == 2
    requires (st'.Peek(0) == 0x273)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
    {
        var st := st';
        // 0x273
        st := JumpDest(st);
        st := Push1(st,0x02);
        // 0x2 0x273
        st := Push1(st,0x00);
        // 0x0 0x2 0x273
        st := Swap(st,1);
        // 0x2 0x0 0x273
        st := SLoad(st);
        // sto[0x2] 0x0 0x273
        st := Swap(st,1);
        // 0x0 sto[0x2] 0x273
        st := Push2(st,0x0100);
        // 0x100 0x0 sto[0x2] 0x273
        assert st.evm.memory == st'.evm.memory;
        assert st.Peek(3) == 0x273;
        st := Exp(st);
        // 0x1 sto[0x2] 0x273
        st := Swap(st,1);
        // sto[0x2] 0x1 0x273
        st := Div(st);
        // sto[0x2] 0x273
        st := Push1(st,0xff);
        // 0xff sto[0x2] 0x273
        st := And(st);
        // (sto[0x2]&0xff) 0x273
        st := Dup(st,2);
        // 0x273 (sto[0x2]&0xff) 0x273
        assume st.IsJumpDest(0x273);
        st := Jump(st);
        // (sto[0x2]&0xff) 0x273
        st := block_0_0x0273(st);
        return st;
    }

    // This block sets up a return frame by writing the value on top the stack
    // on entry (as a byte) into the first word of free memory.  This sequence is
    // surprisingly inefficient.
    method block_0_0x0273(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0273
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x273)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
    {
        ghost var val := st'.Peek(0);
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x40);
        st := MLoad(st);
        // fp val
        st := Dup(st,1);
        // fp fp val
        st := Dup(st,3);
        // val fp fp val
        st := Push1(st,0xff);
        // 0xff val fp fp val
        st := And(st);
        // (val&0xff) fp fp val
        st := Push1(st,0xff);
        // 0xff (val&0xff) fp fp val
        st := And(st);
        // (val&0xff) fp fp val
        assert st.Peek(1) == st.Peek(2) == 0x80;
        assert st.Peek(3) == val;
        st := Dup(st,2);
        // fp (val&0xff) fp fp val
        st := MStore(st);
        // fp fp val
        st := Push1(st,0x20);
        // 0x20 fp fp val
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // (fp+0x20) fp val
        assert (0x20+0x80) % Int.TWO_256 == 0xa0;
        assert st.Peek(0) == 0xa0;
        st := Swap(st,2);
        // val fp (fp+0x20)
        st := Pop(st);
        // fp (fp+0x20)
        st := Pop(st);
        // (fp+0x20)
        st := Push1(st,0x40);
        // 0x40 (fp+0x20)
        st := MLoad(st);
        // fp (fp+0x20)
        st := Dup(st,1);
        // fp fp (fp+0x20)
        st := Swap(st,2);
        // (fp+0x20) fp fp
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        // 0x20 fp
        st := Swap(st,1);
        // fp 0x20
        st := Return(st);
        return st;
    }
}
