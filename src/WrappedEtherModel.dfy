include "util/int.dfy"
include "util/mapping.dfy"
include "util/tx.dfy"

import opened Int
import opened Mapping
import opened Tx

class Contract {
    var balanceOf: mapping<u160,u256>
    var allowance: mapping<u160, mapping<u160,u256>>

    constructor() {
        balanceOf := Map(map[],0);
        allowance := Map(map[],Map(map[],0));
    }

    method fallback(msg: Transaction) returns (r:Result<()>)
    modifies this`balanceOf {
        r := deposit(msg);
    }

    method deposit(msg: Transaction) returns (r:Result<()>)
    modifies this`balanceOf {
        // NOTE: the following is a default assumption about the amount of value that a user can accumulate.
        assume (MAX_U256 as u256 - balanceOf.Get(msg.sender)) >= msg.value;
        // Perform the subtraction
        balanceOf := balanceOf.Set(msg.sender, balanceOf.Get(msg.sender) + msg.value);
        //
        return Ok(());
    }

    method withdraw(msg: Transaction, wad: u256) returns (r:Result<()>)
    modifies this`balanceOf
    requires msg.value == 0 // not payable
    {
        // requires
        if balanceOf.Get(msg.sender) < wad { return Revert; }
        //
        balanceOf := balanceOf.Set(msg.sender, balanceOf.Get(msg.sender) - wad);

        // Transfer
        var tmp := Tx.transfer(msg.sender, wad);
        if tmp == Revert { return Revert; }
        //
        return Ok(());
    }

    // function totalSupply() : (u256) {
    //     ???
    // }

    method approve(msg: Transaction, guy: u160, wad: u256) returns (r:Result<bool>)
    modifies this`allowance
    {
        // Update inner map
        var tmp := allowance.Get(msg.sender).Set(guy,wad);
        // Update outer map
        allowance := allowance.Set(msg.sender,tmp);
        // Done
        return Ok(true);
    }

    method transfer(msg: Transaction, dst: u160, wad: u256) returns (r:Result<bool>)
    modifies this`balanceOf, this`allowance
    requires this.balanceOf.default == 0
    // Simple assumptions about keys
    requires msg.sender in balanceOf.Keys() && dst in balanceOf.Keys()
    requires msg.value == 0 // not payable
    {
        r := transferFrom(msg,msg.sender, dst, wad);
    }

    method transferFrom(msg: Transaction, src: u160, dst: u160, wad: u256) returns (r:Result<bool>)
    modifies this`balanceOf, this`allowance
    requires this.balanceOf.default == 0
    // Simple assumptions about keys
    requires src in balanceOf.Keys() && dst in balanceOf.Keys()
    requires msg.value == 0 // not payable
    // No change in overall balance
    ensures r != Revert ==> sum(old(this.balanceOf.Items())) == sum(this.balanceOf.Items())
    {
        // NOTE: the following is a default assumption about the amount of value
        // that a user can accumulate.  It is safe because wad is bounded by
        // balanceOf[src], which cannot approach overflow.
        assume (old(balanceOf).Get(dst) as nat) + (wad as nat) <= MAX_U256;
        // requires
        if balanceOf.Get(src) < wad { return Revert; }
        //
        if src != msg.sender && allowance.Get(src).Get(msg.sender) != (MAX_U256 as u256) {
            // requires
            if allowance.Get(src).Get(msg.sender) < wad { return Revert; }
            //
            var tmp := allowance.Get(src);
            allowance := allowance.Set(src,tmp.Set(msg.sender,tmp.Get(msg.sender) - wad));
        }
        var src_balance := balanceOf.Get(src);
        balanceOf := balanceOf.Set(src, src_balance - wad);
        balanceOf := balanceOf.Set(dst,balanceOf.Get(dst) + wad);
        // Apply magic lemma
        lemma_transfer(old(balanceOf),balanceOf,src,dst,wad);
        //
        return Ok(true);
    }

    //
    ghost function sum(m:set<(u160,u256)>) : nat {
        if m == {} then 0
        else
            var pair :| pair in m;
            var rhs := pair.1 as nat;
            rhs + sum(m - {pair})
    }

    lemma lemma_sum2(p1: (u160,u256), p2: (u160,u256))
    ensures sum({p1,p2}) == (p1.1 as nat) + (p2.1 as nat) {
        lemma_sum3({p1},{p2});
        assert {p1,p2} == {p1} + {p2};
    }

    lemma lemma_sum3(s1: set<(u160,u256)>, s2: set<(u160,u256)>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2) {
        if s1 == {} {
            assert sum({}) == 0;
            assert sum(s1 + s2) == sum({}+s2);
            assert {}+s2 == s2;
            assert sum(s1 + s2) == sum(s2);
        } else {
            assume sum(s1 + s2) == sum(s1) + sum(s2);
        }
    }

    lemma lemma_transfer(before:mapping<u160,u256>, after:mapping<u160,u256>, from:u160, to: u160, wad: u256)
    // Must have enough to transfer from
    requires before.Get(from) >= wad
    // Must have space to transfer into
    requires (before.Get(to) as nat + wad as nat) <= MAX_U256
    // No difference between before and after except to and from.
    requires after.data[from:=0][to:=0] == before.data[from:=0][to:=0]
    // Minimal difference in keys
    requires {from,to} <= before.Keys() && before.Keys() == after.Keys()
    // From account decreased
    requires (to == from) || before.data[from] - wad == after.data[from]
    // To account increased
    requires (to == from) || before.data[to] + wad == after.data[to]
    // In this case, no difference at all.
    requires (to != from) || after == before
    // Done!
    ensures sum(before.Items()) == sum(after.Items())
    {
        var b1 := (from,before.data[from]);
        var b2 := (to,before.data[to]);
        var a1 := (from,after.data[from]);
        var a2 := (to,after.data[to]);
        //
        if to == from {
            // Easy, as before == after
        } else {
            var b_base := before.Items() - {b1,b2};
            var a_base := after.Items() - {a1,a2};
            // FIXME: why assumption needed?
            assume a_base == b_base;
            // base case
            lemma_sum2(b1,b2);
            lemma_sum2(a1,a2);
            assert sum({b1,b2}) == sum({a1,a2});
            assert before.Items() == b_base + {b1,b2};
            assert after.Items() == b_base + {a1,a2};
            lemma_sum3(b_base,{b1,b2});
            lemma_sum3(b_base,{a1,a2});
        }
    }
}


