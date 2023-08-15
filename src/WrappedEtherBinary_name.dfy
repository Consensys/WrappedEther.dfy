include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module Name {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // name()
    // ============================================================================

    method block_0_0x00b6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x00b6
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push1(st,0xc0);
        assume st.IsJumpDest(0xc0);
        st := JumpI(st);
        if st.PC() == 0xc0 { st := block_0_0x00c0(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method block_0_0x00c0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x00c0
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0xc7);
        st := Push2(st,0x04d7);
        assume st.IsJumpDest(0x4d7);
        st := Jump(st);
        st := block_0_0x04d7(st);
        return st;
    }

    method {:verify false} block_0_0x04d7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x04d7
    requires st'.Operands() == 2
    requires (st'.Peek(0) == 0xc7)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := SLoad(st);
        st := Push1(st,0x01);
        st := Dup(st,2);
        st := Push1(st,0x01);
        st := And(st);
        st := IsZero(st);
        st := Push2(st,0x0100);
        assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
        st := Mul(st);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := And(st);
        st := Push1(st,0x02);
        st := Swap(st,1);
        st := Div(st);
        st := Dup(st,1);
        st := Push1(st,0x1f);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Push1(st,0x20);
        st := Dup(st,1);
        st := Swap(st,2);
        st := Div(st);
        assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
        st := Mul(st);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Swap(st,1);
        st := Dup(st,2);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Push1(st,0x40);
        st := MStore(st);
        st := Dup(st,1);
        st := Swap(st,3);
        st := Swap(st,2);
        st := Swap(st,1);
        st := Dup(st,2);
        st := Dup(st,2);
        st := MStore(st);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Dup(st,3);
        st := Dup(st,1);
        st := SLoad(st);
        st := Push1(st,0x01);
        st := Dup(st,2);
        st := Push1(st,0x01);
        st := And(st);
        st := IsZero(st);
        st := Push2(st,0x0100);
        assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
        st := Mul(st);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := And(st);
        st := Push1(st,0x02);
        st := Swap(st,1);
        st := Div(st);
        st := Dup(st,1);
        st := IsZero(st);
        st := Push2(st,0x056d);
        assume st.IsJumpDest(0x56d);
        st := JumpI(st);
        if st.PC() == 0x56d { st := block_0_0x056d(st); return st; }
        st := Dup(st,1);
        st := Push1(st,0x1f);
        st := Lt(st);
        st := Push2(st,0x0542);
        assume st.IsJumpDest(0x542);
        st := JumpI(st);
        if st.PC() == 0x542 { st := block_0_0x0542(st); return st; }
        st := Push2(st,0x0100);
        st := Dup(st,1);
        st := Dup(st,4);
        st := SLoad(st);
        st := Div(st);
        assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
        st := Mul(st);
        st := Dup(st,4);
        st := MStore(st);
        st := Swap(st,2);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,2);
        st := Push2(st,0x056d);
        assume st.IsJumpDest(0x56d);
        st := Jump(st);
        st := block_0_0x056d(st);
        return st;
    }

    method {:verify false} block_0_0x0542(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0542
    requires st'.Operands() == 8
    requires (st'.Peek(1) == 0x0)
    requires (st'.Peek(4) == 0x0)
    requires (st'.Peek(6) == 0xc7)
    {
        var st := st';
        st := JumpDest(st);
        st := Dup(st,3);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,2);
        st := Swap(st,1);
        st := Push1(st,0x00);
        st := MStore(st);
        st := Push1(st,0x20);
        st := Push1(st,0x00);
        st := Keccak256(st);
        st := Swap(st,1);
        st := block_0_0x0550(st);
        return st;
    }

    method {:verify false} block_0_0x0550(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0550
    requires st'.Operands() == 8
    requires (st'.Peek(4) == 0x0)
    requires (st'.Peek(6) == 0xc7)
    {
        var st := st';
        st := JumpDest(st);
        st := Dup(st,2);
        st := SLoad(st);
        st := Dup(st,2);
        st := MStore(st);
        st := Swap(st,1);
        st := Push1(st,0x01);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Dup(st,1);
        st := Dup(st,4);
        st := Gt(st);
        st := Push2(st,0x0550);
        assume st.IsJumpDest(0x550);
        st := JumpI(st);
        if st.PC() == 0x550 { st := block_0_0x0550(st); return st; }
        st := Dup(st,3);
        st := Swap(st,1);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := Push1(st,0x1f);
        st := And(st);
        st := Dup(st,3);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,2);
        st := block_0_0x056d(st);
        return st;
    }

    method block_0_0x056d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x056d
    requires st'.Operands() == 8
    requires (st'.Peek(4) == 0x0)
    requires (st'.Peek(6) == 0xc7)
    {
        var st := st';
        st := JumpDest(st);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := Dup(st,2);
        assume st.IsJumpDest(0xc7);
        st := Jump(st);
        st := block_0_0x00c7(st);
        return st;
    }

    method {:verify false} block_0_0x00c7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x00c7
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0xc7)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Dup(st,1);
        st := Dup(st,1);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Dup(st,3);
        st := Dup(st,2);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := Dup(st,3);
        st := MStore(st);
        st := Dup(st,4);
        st := Dup(st,2);
        st := Dup(st,2);
        st := MLoad(st);
        st := Dup(st,2);
        st := MStore(st);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,2);
        st := Pop(st);
        st := Dup(st,1);
        st := MLoad(st);
        st := Swap(st,1);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Dup(st,1);
        st := Dup(st,4);
        st := Dup(st,4);
        st := Push1(st,0x00);
        st := block_0_0x00ec(st);
        return st;
    }

    method {:verify false} block_0_0x00ec(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x00ec
    requires st'.Operands() == 12
    requires (st'.Peek(10) == 0xc7)
    {
        var st := st';
        st := JumpDest(st);
        st := Dup(st,4);
        st := Dup(st,2);
        st := Lt(st);
        st := IsZero(st);
        st := Push2(st,0x0106);
        assume st.IsJumpDest(0x106);
        st := JumpI(st);
        if st.PC() == 0x106 { st := block_0_0x0106(st); return st; }
        st := Dup(st,1);
        st := Dup(st,3);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := MLoad(st);
        st := Dup(st,2);
        st := Dup(st,5);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := MStore(st);
        st := Push1(st,0x20);
        st := Dup(st,2);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Pop(st);
        st := Push1(st,0xec);
        assume st.IsJumpDest(0xec);
        st := Jump(st);
        st := block_0_0x00ec(st);
        return st;
    }

    method {:verify false} block_0_0x0106(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0106
    requires st'.Operands() == 12
    requires (st'.Peek(10) == 0xc7)
    {
        var st := st';
        st := JumpDest(st);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := Swap(st,1);
        st := Pop(st);
        st := Swap(st,1);
        st := Dup(st,2);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Push1(st,0x1f);
        st := And(st);
        st := Dup(st,1);
        st := IsZero(st);
        st := Push2(st,0x0133);
        assume st.IsJumpDest(0x133);
        st := JumpI(st);
        if st.PC() == 0x133 { st := block_0_0x0133(st); return st; }
        st := Dup(st,1);
        st := Dup(st,3);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := Dup(st,1);
        st := MLoad(st);
        st := Push1(st,0x01);
        st := Dup(st,4);
        st := Push1(st,0x20);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := Push2(st,0x0100);
        st := Exp(st);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := Not(st);
        st := And(st);
        st := Dup(st,2);
        st := MStore(st);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,2);
        st := Pop(st);
        st := block_0_0x0133(st);
        return st;
    }

    method {:verify false} block_0_0x0133(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0133
    requires st'.Operands() == 7
    requires (st'.Peek(5) == 0xc7)
    {
        var st := st';
        st := JumpDest(st);
        st := Pop(st);
        st := Swap(st,3);
        st := Pop(st);
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