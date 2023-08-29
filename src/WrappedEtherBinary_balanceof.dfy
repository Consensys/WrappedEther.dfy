include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module BalanceOf {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // balanceOf(address)
    // ============================================================================

    method block_0_0x028f(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x028f
    requires st'.Operands() == 1
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x029a);
        assume st.IsJumpDest(0x29a);
        st := JumpI(st);
        if st.PC() == 0x29a { st := block_0_0x029a(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method block_0_0x029a(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x029a
    requires st'.Operands() == 1
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x02c6);
        st := Push1(st,0x04);
        st := Dup(st,1);
        st := Dup(st,1);
        st := CallDataLoad(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := Swap(st,1);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Swap(st,2);
        st := Swap(st,1);
        st := Pop(st);
        st := Pop(st);
        st := Push2(st,0x0b12);
        assume st.IsJumpDest(0xb12);
        st := Jump(st);
        st := block_0_0x0b12(st);
        return st;
    }

    method block_0_0x0b12(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0b12
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x2c6)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x03);
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
        st := Swap(st,1);
        st := Pop(st);
        st := SLoad(st);
        st := Dup(st,2);
        assume st.IsJumpDest(0x2c6);
        st := Jump(st);
        st := block_0_0x02c6(st);
        return st;
    }

    method block_0_0x02c6(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x02c6
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x2c6)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
    {
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