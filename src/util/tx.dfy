include "int.dfy"

module Tx {
    import opened Int

    datatype Transaction = Tx(sender: u160, value: u256)

    datatype Result<T> = Ok(T) | Revert

    method transfer(address: u160, value: u256) returns (r:Result<()>) {
        return Ok(()); // dummy
    }
}