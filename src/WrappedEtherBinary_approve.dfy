include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"

module Approve {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header

    // ============================================================================
    // approve(address,uin256)
    // ============================================================================

    method block_0_0x0141(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0141
    requires st'.Operands() == 1
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        st := JumpDest(st);
        st := CallValue(st);
        st := IsZero(st);
        st := Push2(st,0x014c);
        assume st.IsJumpDest(0x14c);
        st := JumpI(st);
        if st.PC() == 0x14c { st := block_0_0x014c(st); return st; }
        st := Push1(st,0x00);
        st := Dup(st,1);
        st := Revert(st);
        return st;
    }

    method block_0_0x014c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x014c
    requires st'.Operands() == 1
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x0181);
        st := Push1(st,0x04);
        st := Dup(st,1);
        st := Dup(st,1);
        st := CallDataLoad(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := block_0_0x016b(st);
        return st;
    }

    method block_0_0x016b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x016b
    requires st'.Operands() == 5
    requires (st'.Peek(1) == 0x4)
    requires (st'.Peek(2) == 0x4)
    requires (st'.Peek(3) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        // ?z 0x4 0x4 0x181
        st := Swap(st,1);
        // 0x4 ?z 0x4 0x181
        st := Push1(st,0x20);
        // 0x20 0x4 ?z 0x4 0x181
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // 0x24 ?z 0x4 0x181
        st := Swap(st,1);
        // ?z 0x24 0x4 0x181
        st := Swap(st,2);
        // 0x4 0x24 ?z 0x181
        st := Swap(st,1);
        // 0x24 0x4 ?z 0x181
        st := Dup(st,1);
        // 0x24 0x24 0x4 ?z 0x181
        st := CallDataLoad(st);
        // ?x 0x24 0x4 ?z 0x181
        st := block_0_0x0174(st);
        return st;
    }

    method block_0_0x0174(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0174
    requires st'.Operands() == 6
    requires (st'.Peek(1) == 0x24) // for now
    requires (st'.Peek(2) == 0x4)
    requires (st'.Peek(4) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        // ?x 0x24 0x4 ?z 0x181
        st := Swap(st,1);
        // 0x24 ?x 0x4 ?z 0x181
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,1);
        st := Swap(st,2);
        st := Swap(st,1);
        st := Pop(st);
        st := Pop(st);
        st := block_0_0x017d(st);
        return st;
    }

    method block_0_0x017d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x017d
    requires st'.Operands() == 4
    requires (st'.Peek(2) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        st := Push2(st,0x0575);
        assume st.IsJumpDest(0x575);
        st := Jump(st);
        st := block_0_0x0575(st);
        return st;
    }

    method block_0_0x0575(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0575
    requires st'.Operands() == 4
    requires (st'.Peek(2) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        st := JumpDest(st);
        st := Push1(st,0x00);
        st := Dup(st,2);
        st := Push1(st,0x04);
        st := Push1(st,0x00);
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := AndU160(st);
        st := block_0_0x0594(st);
        return st;
    }

    method block_0_0x0594(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0594
    requires st'.Operands() == 9
    requires (st'.Peek(1) == 0x0)
    requires (st'.Peek(2) == 0x4)
    requires (st'.Peek(4) == 0x0)
    requires (st'.Peek(7) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        // addr 0x0 0x4 ?? 0x0 0x181
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        // 0xff.. addr 0x0 0x4 ?? 0x0 0x181
        st := AndU160(st);
        // addr[..160] 0x0 0x4 ?? 0x0 0x181
        st := Dup(st,2);
        // 0x0 addr[..160] 0x0 0x4 ?? 0x0 0x181
        assert st.Peek(0) == st.Peek(2) == st.Peek(5) == 0x00;
        st := MStore(st);
        // 0x0 0x4 ?? 0x0 0x181
        st := Push1(st,0x20);
        // 0x20 0x0 0x4 ?? 0x0 0x181
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // 0x20 0x4 ?? 0x0 0x181
        st := Swap(st,1);
        // 0x4 0x20 ?? 0x0 0x181
        st := Dup(st,2);
        // 0x20 0x4 0x20 ?? 0x0 0x181
        assert st.Peek(4) == 0x00;
        st := block_0_0x05b1(st);
        return st;
    }

    method block_0_0x05b1(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x05b1
    requires st'.Operands() == 9
    requires (st'.Peek(0) == 0x20)
    requires (st'.Peek(1) == 0x4)
    requires (st'.Peek(2) == 0x20)
    requires (st'.Peek(4) == 0x00)
    requires (st'.Peek(7) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        // 0x20 0x4 0x20 ?y 0 ?x ?z 0x181
        st := MStore(st);
        // 0x20 ?y 0x20 ?x ?z 0x181
        st := Push1(st,0x20);
        // 0x20 0x20 ?y 0x20 ?x ?z 0x181
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // 0x40 ?y 0x20 ?x ?z 0x181
        st := Push1(st,0x00);
        // 0x00 0x40 ?y 0x20 ?x ?z 0x181
        st := Keccak256(st);
        // h1 ?y 0x20 ?x ?z 0x181
        st := Push1(st,0x00);
        // 0x00 h1 ?y 0x20 ?x ?z 0x181
        st := Dup(st,6);
        // ?z 0x00 h1 ?y 0x20 ?x ?z 0x181
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        // 0xff.. ?z 0x00 h1 ?y 0x20 ?x ?z 0x181
        st := block_0_0x05d0(st);
        return st;
    }

    method block_0_0x05d0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x05d0
    requires st'.Operands() == 10
    requires (st'.Peek(0) == 0xffffffffffffffffffffffffffffffffffffffff)
    requires (st'.Peek(2) == 0x0)
    requires (st'.Peek(5) == 0x0)
    requires (st'.Peek(8) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        // 0xff.. addr fp
        st := AndU160(st);
        // addr[0..160] fp
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        // 0xff.. addr[0..160] fp
        st := AndU160(st);
        // addr[0..160] fp
        st := Dup(st,2);
        // fp addr[0..160] fp
        st := MStore(st);
        // fp
        st := Push1(st,0x20);
        // 0x20 fp
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // 0xa0 ??
        st := Swap(st,1);
        // ?? 0xa0
        st := block_0_0x05ed(st);
        return st;
    }

    method block_0_0x05ed(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x05ed
    requires st'.Operands() == 8
    requires (st'.Peek(3) == 0x0)
    requires (st'.Peek(6) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires (st'.Peek(1) == 0x20)
    {
        var st := st';
        st := Dup(st,2);
        st := MStore(st);
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Push1(st,0x00);
        st := Keccak256(st);
        st := Dup(st,2);
        st := Swap(st,1);
        st := block_0_0x05f7(st);
        return st;
    }

    method block_0_0x05f7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x05f7
    requires st'.Operands() == 8
    requires (st'.Peek(3) == 0x0)
    requires (st'.Peek(6) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        st := SStore(st);
        st := Pop(st);
        st := Dup(st,3);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := Caller(st);
        st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
        st := And(st);
        st := block_0_0x0627(st);
        return st;
    }

    method block_0_0x0627(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0627
    requires st'.Operands() == 7
    requires (st'.Peek(2) == 0x0)
    requires (st'.Peek(5) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        st := PushN(st,32,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
        st := Dup(st,5);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Dup(st,1);
        st := Dup(st,3);
        st := Dup(st,2);
        st := MStore(st);
        st := block_0_0x0650(st);
        return st;
    }

    method block_0_0x0650(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0650
    requires st'.Operands() == 11
    requires (st'.Peek(3) == 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925)
    requires (st'.Peek(6) == 0x0)
    requires (st'.Peek(9) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    requires (st'.Peek(0) == st'.Read(0x40) == 0x80)
    {
        var st := st';
        st := Push1(st,0x20);
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        st := Swap(st,2);
        st := Pop(st);
        st := Pop(st);
        st := Push1(st,0x40);
        st := MLoad(st);
        st := Dup(st,1);
        st := block_0_0x065a(st);
        return st;
    }

    method block_0_0x065a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x065a
    requires st'.Operands() == 11
    requires (st'.Peek(1) <= st'.Peek(2))
    requires (st'.Peek(3) == 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925)
    requires (st'.Peek(6) == 0x0)
    requires (st'.Peek(9) == 0x181)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        st := Swap(st,2);
        assert st.Peek(1) <= st.Peek(0);
        st := Sub(st);
        st := Swap(st,1);
        st := LogN(st,3);
        st := Push1(st,0x01);
        st := Swap(st,1);
        st := Pop(st);
        st := Swap(st,3);
        st := block_0_0x0663(st);
        return st;
    }

    method block_0_0x0663(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0663
    requires st'.Operands() == 5
    requires (st'.Peek(0) == 0x181)
    requires (st'.Peek(3) == 0x1)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
    {
        var st := st';
        // 0x181 ?? ?? 0x1 ??
        st := Swap(st,2);
        // ?? ?? 0x181 0x1 ??
        st := Pop(st);
        // ?? 0x181 0x1 ??
        st := Pop(st);
        // 0x181 0x1 ??
        assume st.IsJumpDest(0x181);
        st := Jump(st);
        st := block_0_0x0181(st);
        return st;
    }

    method block_0_0x0181(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0181
    requires st'.Operands() == 2
    requires (st'.Peek(0) == 0x1)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80
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
