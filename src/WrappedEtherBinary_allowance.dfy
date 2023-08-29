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
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
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

    method block_0_0x03d9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x03d9
    requires st'.Operands() == 1
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    requires st'.evm.context.callValue == 0
    {
        var st := st';
        st := JumpDest(st);
        st := Push2(st,0x0424);
        // 0x424 ?
        st := Push1(st,0x04);
        // 0x4 0x424 ?
        st := Dup(st,1);
        // 0x4 0x4 0x424 ?
        st := Dup(st,1);
        // 0x4 0x4 0x4 0x424 ?
        st := CallDataLoad(st);
        // sender 0x4 0x4 0x424 ?
        st := PushN(st,20,0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff);
        assert st.Peek(0) as nat == Int.MAX_U160; // sanity check
        // 0xff.. sender 0x4 0x4 0x424 ?
        st := AndU160(st);
        // sender[..160] 0x4 0x4 0x424 ?
        st := Swap(st,1);
        // 0x4 sender[..160] 0x4 0x424 ?
        st := Push1(st,0x20);
        // 0x20 0x4 sender[..160] 0x4 0x424 ?
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // 0x24 sender[..160] 0x4 0x424 ?
        st := Swap(st,1);
        // sender[..160] 0x24 0x4 0x424 ?
        st := Swap(st,2);
        // 0x4 0x24 sender[..160] 0x424 ?
        st := Swap(st,1);
        // 0x24 0x4 sender[..160] 0x424 ?
        st := Dup(st,1);
        // 0x24 0x24 0x4 sender[..160] 0x424 ?
        assert (st.Peek(0) == st.Peek(1) == 0x24) && st.Peek(4) == 0x424 && st.Operands() == 6;
        st := CallDataLoad(st);
        // guy 0x24 0x4 sender[..160] 0x424 ?
        st := PushN(st,20,0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff);
        assert st.Peek(0) as nat == Int.MAX_U160; // sanity check
        // 0xff.. guy 0x24 0x4 sender[..160] 0x424 ?
        st := AndU160(st);
        // guy[..160] 0x24 0x4 sender[..160] 0x424 ?
        st := Swap(st,1);
        // 0x24 guy[..160] 0x4 sender[..160] 0x424 ?
        assert st.Peek(0) == 0x24 && st.Operands() == 6;
        st := Push1(st,0x20);
        // 0x20 0x24 guy[..160] 0x4 sender[..160] 0x424 ?
        assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
        st := Add(st);
        // 0x44 guy[..160] 0x4 sender[..160] 0x424 ?
        assert st.Peek(4) == 0x424;
        st := Swap(st,1);
        // guy[..160] 0x44 0x4 sender[..160] 0x424 ?
        st := Swap(st,2);
        // 0x4 0x44 guy[..160] sender[..160] 0x424 ?
        st := Swap(st,1);
        // 0x44 0x4 guy[..160] sender[..160] 0x424 ?
        st := Pop(st);
        // 0x4 guy[..160] sender[..160] 0x424 ?
        st := Pop(st);
        // guy[..160] sender[..160] 0x424 ?
        st := Push2(st,0x0bdd);
        assume st.IsJumpDest(0xbdd);
        st := Jump(st);
        st := block_0_0x0bdd(st);
        return st;
    }

    method block_0_0x0bdd(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0bdd
    requires st'.Operands() == 4
    requires (st'.Peek(2) == 0x424)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
    {
        ghost var sender := st'.Peek(1);
        ghost var guy := st'.Peek(0);
        var st := st';
        st := JumpDest(st);
        // guy sender 0x424 ?
        st := Push1(st,0x04); // slot number?
        // 0x4 guy sender 0x424 ?
        st := Push1(st,0x20);
        // 0x20 0x4 guy sender 0x424 ?
        st := MStore(st);
        // guy sender 0x424 ? | mem[0x20:=0x4]
        st := Dup(st,2);
        // sender guy sender 0x424 ? | mem[0x20:=0x4]
        st := Push1(st,0x00);
        // 0x00 sender guy sender 0x424 ? | mem[0x20:=0x4]
        st := MStore(st);
        // guy sender 0x424 ? | mem[0x00:=sender,0x20:=0x4]
        assert st.Peek(2) == 0x424;
        assert st.Operands() == 4;
        st := Push1(st,0x40);
        // 0x40 guy sender 0x424 ? | mem[0x00:=sender,0x20:=0x4]
        st := Push1(st,0x00);
        // 0x00 0x40 guy sender 0x424 ? | mem[0x00:=sender,0x20:=0x4]
        st := Keccak256(st); // 0x4; sender
        // h1 guy sender 0x424 ? | mem[0x00:=sender,0x20:=0x4]
        st := Push1(st,0x20);
        // 0x20 h guy sender 0x424 ? | mem[0x00:=sender,0x20:=0x4]
        st := MStore(st);
        // guy sender 0x424 ? | mem[0x00:=sender,0x20:=h1]
        st := Dup(st,1);
        // guy guy sender 0x424 ? | mem[0x00:=sender,0x20:=h1]
        st := Push1(st,0x00);
        // 0x00 guy guy sender 0x424 ? | mem[0x00:=sender,0x20:=h1]
        st := MStore(st);
        // guy sender 0x424 ? | mem[0x00:=guy,0x20:=h1]
        assert st.Peek(2) == 0x424;
        assert st.Operands() == 4;
        st := Push1(st,0x40);
        // 0x40 guy sender 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := Push1(st,0x00);
        // 0x00 0x40 guy sender 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := Keccak256(st);
        // h2 guy sender 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := Push1(st,0x00);
        // 0x00 h2 guy sender 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := Swap(st,2);
        // guy h2 0x00 sender 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := Pop(st);
        // h2 0x00 sender 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := Swap(st,2);
        // sender 0x00 h2 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := Pop(st);
        // 0x00 h2 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := Pop(st);
        // h2 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := SLoad(st);
        // wad 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := Dup(st,2);
        // 0x424 wad 0x424 ? | mem[0x00:=guy,0x20:=h1]
        assume st.IsJumpDest(0x424);
        st := Jump(st);
        // wad 0x424 ? | mem[0x00:=guy,0x20:=h1]
        st := block_0_0x0424(st);
        return st;
    }

    method block_0_0x0424(st': EvmState.ExecutingState) returns (st'': EvmState.TerminatedState)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0424
    requires st'.Operands() == 3
    requires (st'.Peek(1) == 0x424)
    requires Memory.Size(st'.evm.memory) >= 0x60 && st'.Read(0x40) == 0x80 // added by djp
    //
    ensures st''.RETURNS?
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
