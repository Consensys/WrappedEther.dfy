include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module Symbol {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // symbol()
    // ============================================================================

    method block_0_0x02dc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x02dc
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x02e7);
        assume st.IsJumpDest(0x2e7);
        st := JumpI(st);
        if st.PC() == 0x2e7 { st := block_0_0x02e7(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method block_0_0x02e7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x02e7
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x02ef);
        st := Push2(st,0x0b2a);
        assume st.IsJumpDest(0xb2a);
        st := Jump(st);
        st := block_0_0x0b2a(st);
        return st;
    }

    method {:verify false} block_0_0x0b2a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0b2a
    requires st'.Operands() == 2
    requires (st'.Peek(0) == 0x2ef)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x01);
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
        st := Push2(st,0x0bc0);
        assume st.IsJumpDest(0xbc0);
        st := JumpI(st);
        if st.PC() == 0xbc0 { st := block_0_0x0bc0(st); return st; }
        st := Dup(st,1);
        st := Push1(st,0x1f);
        st := Lt(st);
        st := Push2(st,0x0b95);
        assume st.IsJumpDest(0xb95);
        st := JumpI(st);
        if st.PC() == 0xb95 { st := block_0_0x0b95(st); return st; }
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
        st := Push2(st,0x0bc0);
        assume st.IsJumpDest(0xbc0);
        st := Jump(st);
        st := block_0_0x0bc0(st);
        return st;
    }

    method {:verify false} block_0_0x0b95(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0b95
    requires st'.Operands() == 8
    requires (st'.Peek(1) == 0x1)
    requires (st'.Peek(4) == 0x1)
    requires (st'.Peek(6) == 0x2ef)
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
        st := block_0_0x0ba3(st);
        return st;
    }

    method {:verify false} block_0_0x0ba3(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0ba3
    requires st'.Operands() == 8
    requires (st'.Peek(4) == 0x1)
    requires (st'.Peek(6) == 0x2ef)
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
        st := Push2(st,0x0ba3);
        assume st.IsJumpDest(0xba3);
        st := JumpI(st);
        if st.PC() == 0xba3 { st := block_0_0x0ba3(st); return st; }
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
        st := block_0_0x0bc0(st);
        return st;
    }

    method block_0_0x0bc0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0bc0
    requires st'.Operands() == 8
    requires (st'.Peek(4) == 0x1)
    requires (st'.Peek(6) == 0x2ef)
    {
        var st := st';
        st := JumpDest(st);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        st := Dup(st,2);
        assume st.IsJumpDest(0x2ef);
        st := Jump(st);
        st := block_0_0x02ef(st);
        return st;
    }

    method {:verify false} block_0_0x02ef(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x02ef
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x2ef)
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
        st := block_0_0x0314(st);
        return st;
    }

    method {:verify false} block_0_0x0314(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0314
    requires st'.Operands() == 12
    requires (st'.Peek(10) == 0x2ef)
    {
        var st := st';
        st := JumpDest(st);
        st := Dup(st,4);
        st := Dup(st,2);
        st := Lt(st);
        st := IsZero(st);
        st := Push2(st,0x032f);
        assume st.IsJumpDest(0x32f);
        st := JumpI(st);
        if st.PC() == 0x32f { st := block_0_0x032f(st); return st; }
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
        st := Push2(st,0x0314);
        assume st.IsJumpDest(0x314);
        st := Jump(st);
        st := block_0_0x0314(st);
        return st;
    }

    method {:verify false} block_0_0x032f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x032f
    requires st'.Operands() == 12
    requires (st'.Peek(10) == 0x2ef)
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
        st := Push2(st,0x035c);
        assume st.IsJumpDest(0x35c);
        st := JumpI(st);
        if st.PC() == 0x35c { st := block_0_0x035c(st); return st; }
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
        st := block_0_0x035c(st);
        return st;
    }

    method {:verify false} block_0_0x035c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x035c
    requires st'.Operands() == 7
    requires (st'.Peek(5) == 0x2ef)
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