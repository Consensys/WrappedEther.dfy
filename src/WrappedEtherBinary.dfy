include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/core/code.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"
include "WrappedEtherBinary_header.dfy"
include "WrappedEtherBinary_allowance.dfy"
include "WrappedEtherBinary_approve.dfy"
include "WrappedEtherBinary_balanceof.dfy"
include "WrappedEtherBinary_decimals.dfy"
include "WrappedEtherBinary_deposit.dfy"
include "WrappedEtherBinary_name.dfy"
include "WrappedEtherBinary_symbol.dfy"
include "WrappedEtherBinary_totalsupply.dfy"
include "WrappedEtherBinary_transferfrom.dfy"
include "WrappedEtherBinary_withdraw.dfy"

module Main {
    import opened Opcode
    import opened Code
    import opened Memory
    import opened Bytecode
    import opened Header
    import Approve
    import Allowance
    import BalanceOf
    import Decimals
    import Deposit
    import Name
    import Symbol
    import TotalSupply
    import TransferFrom
    import Withdraw

    method {:verify false} block_0_0x0000(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(BYTECODE_0)
    requires st'.WritesPermitted() && st'.PC() == 0x0000
    requires st'.Operands() == 0
    {
        var st := st';
        st := Push1(st,0x60);
        st := Push1(st,0x40);
        st := MStore(st);
        st := Push1(st,0x04);
        st := CallDataSize(st);
        st := Lt(st);
        st := Push1(st,0xad);
        assume st.IsJumpDest(0xad);
        st := JumpI(st);
        if st.PC() == 0xad { st := Deposit.block_0_0x00ad(st); return st; }
        st := Push1(st,0x00);
        st := CallDataLoad(st);
        st := PushN(st,29,0x0100000000000000000000000000000000000000000000000000000000);
        st := Swap(st,1);
        st := Div(st);
        st := Push4(st,0xffffffff);
        st := And(st);
        st := Dup(st,1);
        st := Push4(st,0x06fdde03); // name()
        st := Eq(st);
        st := Push1(st,0xb6);
        assume st.IsJumpDest(0xb6);
        st := JumpI(st);
        if st.PC() == 0xb6 { st := Name.block_0_0x00b6(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0x095ea7b3); // approve(address,uin256)
        st := Eq(st);
        st := Push2(st,0x0141);
        assume st.IsJumpDest(0x141);
        st := JumpI(st);
        if st.PC() == 0x141 { st := Approve.block_0_0x0141(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0x18160ddd); // totalSupply()
        st := Eq(st);
        st := Push2(st,0x019b);
        assume st.IsJumpDest(0x19b);
        st := JumpI(st);
        if st.PC() == 0x19b { st := TotalSupply.block_0_0x019b(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0x23b872dd); // transferFrom(address,address,uint256)
        st := Eq(st);
        st := Push2(st,0x01c4);
        assume st.IsJumpDest(0x1c4);
        st := JumpI(st);
        if st.PC() == 0x1c4 { st := TransferFrom.block_0_0x01c4(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0x2e1a7d4d); // withdraw(uint256)
        st := Eq(st);
        st := Push2(st,0x023d);
        assume st.IsJumpDest(0x23d);
        st := JumpI(st);
        if st.PC() == 0x23d { st := Withdraw.block_0_0x023d(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0x313ce567); // decimals()
        st := Eq(st);
        st := Push2(st,0x0260);
        assume st.IsJumpDest(0x260);
        st := JumpI(st);
        if st.PC() == 0x260 { st := Decimals.block_0_0x0260(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0x70a08231); // balanceOf(address)
        st := Eq(st);
        st := Push2(st,0x028f);
        assume st.IsJumpDest(0x28f);
        st := JumpI(st);
        if st.PC() == 0x28f { st := BalanceOf.block_0_0x028f(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0x95d89b41); // symbol()
        st := Eq(st);
        st := Push2(st,0x02dc);
        assume st.IsJumpDest(0x2dc);
        st := JumpI(st);
        if st.PC() == 0x2dc { st := Symbol.block_0_0x02dc(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0xa9059cbb); // transfer(address,uint256)
        st := Eq(st);
        st := Push2(st,0x036a);
        assume st.IsJumpDest(0x36a);
        st := JumpI(st);
        if st.PC() == 0x36a { st := TransferFrom.block_0_0x036a(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0xd0e30db0); // deposit()
        st := Eq(st);
        st := Push2(st,0x03c4);
        assume st.IsJumpDest(0x3c4);
        st := JumpI(st);
        if st.PC() == 0x3c4 { st := Deposit.block_0_0x03c4(st); return st; }
        st := Dup(st,1);
        st := Push4(st,0xdd62ed3e); // allowance(address,address)
        st := Eq(st);
        st := Push2(st,0x03ce);
        assume st.IsJumpDest(0x3ce);
        st := JumpI(st);
        if st.PC() == 0x3ce { st := Allowance.block_0_0x03ce(st); return st; }
        st := Deposit.block_0_0x00ad(st);
        return st;
    }

    // NOTE: What are these trailing bytes?  It maybe deadcode (since this contract
    // was deployed in 2017).  Recall bug identified by Dedaub in 2022:
    // https://github.com/ethereum/solidity/issues/13680
    //
    // 0x00a165627a7a72305820deb4c2ccab3c2fdca32ab3f46728389c2fe2c165d5fafa07661e4e004f6c344a0029
}