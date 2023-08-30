include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module TransferFrom {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // transferFrom(address,address,uint256)
    // ============================================================================

    method block_0_0x01c4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x01c4
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x01cf);
        assume st.IsJumpDest(0x1cf);
        st := JumpI(st);
        if st.PC() == 0x1cf { st := block_0_0x01cf(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method {:verify false} block_0_0x01cf(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x01cf
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x0223);
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
        st := Push2(st,0x0686);
        assume st.IsJumpDest(0x686);
        st := Jump(st);
        st := block_0_0x0686(st);
        return st;
    }

    method {:verify false} block_0_0x0686(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0686
    requires 5 <= st'.Operands() <= 9
    requires (st'.Peek(3) == 0x223) || (st'.Peek(3) == 0xbd5)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x00);
        st := Dup(st,2);
        st := Push1(st,0x03);
        st := Push1(st,0x00);
        st := Dup(st,7);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
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
        st := Push2(st,0x06d6);
        assume st.IsJumpDest(0x6d6);
        st := JumpI(st);
        if st.PC() == 0x6d6 { st := block_0_0x06d6(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method {:verify false} block_0_0x06d6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x06d6
    requires 6 <= st'.Operands() <= 10
    requires (st'.Peek(0) == 0x0)
    requires (st'.Peek(4) == 0x223) || (st'.Peek(4) == 0xbd5)
    {
        var st := st';
        st := JumpDest(st);
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := Dup(st,5);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := Eq(st);
        st := IsZero(st);
        st := Dup(st,1);
        st := IsZero(st);
        st := Push2(st,0x07ae);
        assume st.IsJumpDest(0x7ae);
        st := JumpI(st);
        if st.PC() == 0x7ae { st := block_0_0x07ae(st); return st; }
        st := Pop(st);
        st := PushN(st,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
        st := Push1(st,0x04);
        st := Push1(st,0x00);
        st := Dup(st,7);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
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
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
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
        st := Eq(st);
        st := IsZero(st);
        st := block_0_0x07ae(st);
        return st;
    }

    method {:verify false} block_0_0x07ae(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x07ae
    requires 7 <= st'.Operands() <= 11
    requires (st'.Peek(1) == 0x0)
    requires (st'.Peek(5) == 0x223) || (st'.Peek(5) == 0xbd5)
    {
        var st := st';
        st := JumpDest(st);
        st := IsZero(st);
        st := Push2(st,0x08c9);
        assume st.IsJumpDest(0x8c9);
        st := JumpI(st);
        if st.PC() == 0x8c9 { st := block_0_0x08c9(st); return st; }
        st := Dup(st,2);
        st := Push1(st,0x04);
        st := Push1(st,0x00);
        st := Dup(st,7);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
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
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
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
        st := Push2(st,0x083e);
        assume st.IsJumpDest(0x83e);
        st := JumpI(st);
        if st.PC() == 0x83e { st := block_0_0x083e(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method {:verify false} block_0_0x083e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x083e
    requires 6 <= st'.Operands() <= 10
    requires (st'.Peek(0) == 0x0)
    requires (st'.Peek(4) == 0x223) || (st'.Peek(4) == 0xbd5)
    {
        var st := st';
        st := JumpDest(st);
        st := Dup(st,2);
        st := Push1(st,0x04);
        st := Push1(st,0x00);
        st := Dup(st,7);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
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
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
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
        st := block_0_0x08c9(st);
        return st;
    }

    method {:verify false} block_0_0x08c9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x08c9
    requires 6 <= st'.Operands() <= 10
    requires (st'.Peek(0) == 0x0)
    requires (st'.Peek(4) == 0x223) || (st'.Peek(4) == 0xbd5)
    {
        var st := st';
        st := JumpDest(st);
        st := Dup(st,2);
        st := Push1(st,0x03);
        st := Push1(st,0x00);
        st := Dup(st,7);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
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
        st := Dup(st,2);
        st := Push1(st,0x03);
        st := Push1(st,0x00);
        st := Dup(st,6);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
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
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,3);
        st := Pop(st);
        st := Pop(st);
        st := Dup(st,2);
        st := Swap(st,1);
        st := SStore(st);
        st := Pop(st);
        st := Dup(st,3);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := Dup(st,5);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := PushN(st,32,0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
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
        st := Swap(st,4);
        st := Swap(st,3);
        st := Pop(st);
        st := Pop(st);
        st := Pop(st);
        assume st.IsJumpDest(0x223);
        assume st.IsJumpDest(0xbd5);
        st := Jump(st);
        match st.PC() {
            case 0x223 => { st := block_0_0x0223(st); }
            case 0xbd5 => { st := block_0_0x0bd5(st); } // ==> transfer
        }
        return st;
    }

    method {:verify false} block_0_0x0223(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0223
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


    // ============================================================================
    // transfer(address,uint256)
    // ============================================================================

    method block_0_0x036a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x036a
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x0375);
        assume st.IsJumpDest(0x375);
        st := JumpI(st);
        if st.PC() == 0x375 { st := block_0_0x0375(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method {:verify false} block_0_0x0375(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0375
    requires st'.Operands() == 1
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x03aa);
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
        st := Push2(st,0x0bc8);
        assume st.IsJumpDest(0xbc8);
        st := Jump(st);
        st := block_0_0x0bc8(st);
        return st;
    }

    method block_0_0x0bc8(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0bc8
    requires st'.Operands() == 4
    requires (st'.Peek(2) == 0x3aa)
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x00);
        st := Push2(st,0x0bd5);
        st := Caller(st);
        st := Dup(st,5);
        st := Dup(st,5);
        st := Push2(st,0x0686);
        assume st.IsJumpDest(0x686);
        st := Jump(st);
        st := block_0_0x0686(st); // call transferFrom()
        return st;
    }

    // return from transferFrom()
    method block_0_0x0bd5(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0bd5
    requires st'.Operands() == 6
    requires (st'.Peek(0) == 0x1)
    requires (st'.Peek(1) == 0x0)
    requires (st'.Peek(4) == 0x3aa)
    {
        var st := st';
        st := JumpDest(st);
        st := Swap(st,1);
        st := Pop(st);
        st := Swap(st,3);
        st := Swap(st,2);
        st := Pop(st);
        st := Pop(st);
        assume st.IsJumpDest(0x3aa);
        st := Jump(st);
        st := block_0_0x03aa(st);
        return st;
    }

    method {:verify false} block_0_0x03aa(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x03aa
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