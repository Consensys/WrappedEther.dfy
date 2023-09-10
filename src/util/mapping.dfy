module Mapping {
    datatype mapping<S,T> = Map(data:map<S,T>, default: T) {
        function Get(from: S) : (r:T)
        ensures from in data.Keys || r == default {
            if from in data.Keys
            then
                data[from]
            else
                default
        }

        function Contains(from: S) : bool {
            from in this.data.Keys
        }

        function Keys() : set<S> { this.data.Keys }

        function Items() : set<(S,T)> { this.data.Items }

        function Set(from: S, item: T) : (r:mapping<S,T>)
        ensures from in data.Keys ==> (data.Keys == r.data.Keys)
        ensures forall i :: i in data.Keys ==> i in r.data.Keys
        ensures forall i :: i in r.data.Keys ==> (i == from || i in data.Keys)
        ensures forall i :: (i in data.Keys && i != from) ==> (data[i] == r.data[i])
        ensures !(from in data.Keys) ==> (data.Keys == (r.data.Keys-{from})) {
           this.(data:=data[from:=item])
        }
    }
    // class Mapping<S(==),T> {
    //     var data: map<S,T>;
    //     var default: T;

    //     constructor(default: T) {
    //         this.data := map[];
    //         this.default := default;
    //     }

    //     function Disjoint() : bool
    //     reads this`data {
    //         forall i, j :: (i in this.data && j in this.data && i != j) ==> this.data[i] != this.data[j]
    //     }

    //     function Keys() : set<S>
    //     reads this`data {
    //         this.data.Keys
    //     }

    //     function Values() : set<T>
    //     reads this`data {
    //         this.data.Values
    //     }

    //     function Get(from: S) : T
    //     reads this {
    //         if from in this.data
    //         then
    //             this.data[from]
    //         else
    //             // PROBLEM
    //             this.default
    //     }

    //     method Set(from: S, item: T)
    //     modifies this`data {
    //         this.data := this.data[from:=item];
    //     }
    // }
}
