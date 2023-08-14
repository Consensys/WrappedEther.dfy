include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/evms/berlin.dfy"

//import Int`{u8,u160}
import opened Opcode
import opened Memory
import opened Bytecode

type u8 = Int.u8
type u160 = Int.u160
type u256 = Int.u256
const MAX_U256 : nat := Int.MAX_U256

method external_call(sender: u160, st: EvmState.ExecutingState) returns (r:EvmState.TerminatedState)
ensures r.RETURNS? ==> r.world.Exists(sender) {
	 return EvmState.ERROR(EvmState.INSUFFICIENT_GAS); // dummy
}

const BYTECODE_0 : seq<u8> := [0x60, 0x60, 0x60, 0x40, 0x52, 0x60, 0x4, 0x36, 0x10, 0x60, 0xad, 0x57, 0x60, 0x0, 0x35, 0x7c, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x90, 0x4, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x80, 0x63, 0x6, 0xfd, 0xde, 0x3, 0x14, 0x60, 0xb6, 0x57, 0x80, 0x63, 0x9, 0x5e, 0xa7, 0xb3, 0x14, 0x61, 0x1, 0x41, 0x57, 0x80, 0x63, 0x18, 0x16, 0xd, 0xdd, 0x14, 0x61, 0x1, 0x9b, 0x57, 0x80, 0x63, 0x23, 0xb8, 0x72, 0xdd, 0x14, 0x61, 0x1, 0xc4, 0x57, 0x80, 0x63, 0x2e, 0x1a, 0x7d, 0x4d, 0x14, 0x61, 0x2, 0x3d, 0x57, 0x80, 0x63, 0x31, 0x3c, 0xe5, 0x67, 0x14, 0x61, 0x2, 0x60, 0x57, 0x80, 0x63, 0x70, 0xa0, 0x82, 0x31, 0x14, 0x61, 0x2, 0x8f, 0x57, 0x80, 0x63, 0x95, 0xd8, 0x9b, 0x41, 0x14, 0x61, 0x2, 0xdc, 0x57, 0x80, 0x63, 0xa9, 0x5, 0x9c, 0xbb, 0x14, 0x61, 0x3, 0x6a, 0x57, 0x80, 0x63, 0xd0, 0xe3, 0xd, 0xb0, 0x14, 0x61, 0x3, 0xc4, 0x57, 0x80, 0x63, 0xdd, 0x62, 0xed, 0x3e, 0x14, 0x61, 0x3, 0xce, 0x57, 0x5b, 0x60, 0xb4, 0x61, 0x4, 0x3a, 0x56, 0x5b, 0x0, 0x5b, 0x34, 0x15, 0x60, 0xc0, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x60, 0xc7, 0x61, 0x4, 0xd7, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x80, 0x60, 0x20, 0x1, 0x82, 0x81, 0x3, 0x82, 0x52, 0x83, 0x81, 0x81, 0x51, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x80, 0x51, 0x90, 0x60, 0x20, 0x1, 0x90, 0x80, 0x83, 0x83, 0x60, 0x0, 0x5b, 0x83, 0x81, 0x10, 0x15, 0x61, 0x1, 0x6, 0x57, 0x80, 0x82, 0x1, 0x51, 0x81, 0x84, 0x1, 0x52, 0x60, 0x20, 0x81, 0x1, 0x90, 0x50, 0x60, 0xec, 0x56, 0x5b, 0x50, 0x50, 0x50, 0x50, 0x90, 0x50, 0x90, 0x81, 0x1, 0x90, 0x60, 0x1f, 0x16, 0x80, 0x15, 0x61, 0x1, 0x33, 0x57, 0x80, 0x82, 0x3, 0x80, 0x51, 0x60, 0x1, 0x83, 0x60, 0x20, 0x3, 0x61, 0x1, 0x0, 0xa, 0x3, 0x19, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x5b, 0x50, 0x92, 0x50, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x1, 0x4c, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x1, 0x81, 0x60, 0x4, 0x80, 0x80, 0x35, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x5, 0x75, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x1, 0xa6, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x1, 0xae, 0x61, 0x6, 0x67, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x1, 0xcf, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x2, 0x23, 0x60, 0x4, 0x80, 0x80, 0x35, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x80, 0x35, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x6, 0x86, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x2, 0x48, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x2, 0x5e, 0x60, 0x4, 0x80, 0x80, 0x35, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x9, 0xd3, 0x56, 0x5b, 0x0, 0x5b, 0x34, 0x15, 0x61, 0x2, 0x6b, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x2, 0x73, 0x61, 0xa, 0xff, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x60, 0xff, 0x16, 0x60, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x2, 0x9a, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x2, 0xc6, 0x60, 0x4, 0x80, 0x80, 0x35, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0xb, 0x12, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x2, 0xe7, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x2, 0xef, 0x61, 0xb, 0x2a, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x80, 0x60, 0x20, 0x1, 0x82, 0x81, 0x3, 0x82, 0x52, 0x83, 0x81, 0x81, 0x51, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x80, 0x51, 0x90, 0x60, 0x20, 0x1, 0x90, 0x80, 0x83, 0x83, 0x60, 0x0, 0x5b, 0x83, 0x81, 0x10, 0x15, 0x61, 0x3, 0x2f, 0x57, 0x80, 0x82, 0x1, 0x51, 0x81, 0x84, 0x1, 0x52, 0x60, 0x20, 0x81, 0x1, 0x90, 0x50, 0x61, 0x3, 0x14, 0x56, 0x5b, 0x50, 0x50, 0x50, 0x50, 0x90, 0x50, 0x90, 0x81, 0x1, 0x90, 0x60, 0x1f, 0x16, 0x80, 0x15, 0x61, 0x3, 0x5c, 0x57, 0x80, 0x82, 0x3, 0x80, 0x51, 0x60, 0x1, 0x83, 0x60, 0x20, 0x3, 0x61, 0x1, 0x0, 0xa, 0x3, 0x19, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x5b, 0x50, 0x92, 0x50, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x3, 0x75, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x3, 0xaa, 0x60, 0x4, 0x80, 0x80, 0x35, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0xb, 0xc8, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x61, 0x3, 0xcc, 0x61, 0x4, 0x3a, 0x56, 0x5b, 0x0, 0x5b, 0x34, 0x15, 0x61, 0x3, 0xd9, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x4, 0x24, 0x60, 0x4, 0x80, 0x80, 0x35, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x80, 0x35, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0xb, 0xdd, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x34, 0x60, 0x3, 0x60, 0x0, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x82, 0x82, 0x54, 0x1, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0xe1, 0xff, 0xfc, 0xc4, 0x92, 0x3d, 0x4, 0xb5, 0x59, 0xf4, 0xd2, 0x9a, 0x8b, 0xfc, 0x6c, 0xda, 0x4, 0xeb, 0x5b, 0xd, 0x3c, 0x46, 0x7, 0x51, 0xc2, 0x40, 0x2c, 0x5c, 0x5c, 0xc9, 0x10, 0x9c, 0x34, 0x60, 0x40, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xa2, 0x56, 0x5b, 0x60, 0x0, 0x80, 0x54, 0x60, 0x1, 0x81, 0x60, 0x1, 0x16, 0x15, 0x61, 0x1, 0x0, 0x2, 0x3, 0x16, 0x60, 0x2, 0x90, 0x4, 0x80, 0x60, 0x1f, 0x1, 0x60, 0x20, 0x80, 0x91, 0x4, 0x2, 0x60, 0x20, 0x1, 0x60, 0x40, 0x51, 0x90, 0x81, 0x1, 0x60, 0x40, 0x52, 0x80, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x20, 0x1, 0x82, 0x80, 0x54, 0x60, 0x1, 0x81, 0x60, 0x1, 0x16, 0x15, 0x61, 0x1, 0x0, 0x2, 0x3, 0x16, 0x60, 0x2, 0x90, 0x4, 0x80, 0x15, 0x61, 0x5, 0x6d, 0x57, 0x80, 0x60, 0x1f, 0x10, 0x61, 0x5, 0x42, 0x57, 0x61, 0x1, 0x0, 0x80, 0x83, 0x54, 0x4, 0x2, 0x83, 0x52, 0x91, 0x60, 0x20, 0x1, 0x91, 0x61, 0x5, 0x6d, 0x56, 0x5b, 0x82, 0x1, 0x91, 0x90, 0x60, 0x0, 0x52, 0x60, 0x20, 0x60, 0x0, 0x20, 0x90, 0x5b, 0x81, 0x54, 0x81, 0x52, 0x90, 0x60, 0x1, 0x1, 0x90, 0x60, 0x20, 0x1, 0x80, 0x83, 0x11, 0x61, 0x5, 0x50, 0x57, 0x82, 0x90, 0x3, 0x60, 0x1f, 0x16, 0x82, 0x1, 0x91, 0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x81, 0x56, 0x5b, 0x60, 0x0, 0x81, 0x60, 0x4, 0x60, 0x0, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x85, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x81, 0x90, 0x55, 0x50, 0x82, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0x8c, 0x5b, 0xe1, 0xe5, 0xeb, 0xec, 0x7d, 0x5b, 0xd1, 0x4f, 0x71, 0x42, 0x7d, 0x1e, 0x84, 0xf3, 0xdd, 0x3, 0x14, 0xc0, 0xf7, 0xb2, 0x29, 0x1e, 0x5b, 0x20, 0xa, 0xc8, 0xc7, 0xc3, 0xb9, 0x25, 0x84, 0x60, 0x40, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xa3, 0x60, 0x1, 0x90, 0x50, 0x92, 0x91, 0x50, 0x50, 0x56, 0x5b, 0x60, 0x0, 0x30, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x31, 0x90, 0x50, 0x90, 0x56, 0x5b, 0x60, 0x0, 0x81, 0x60, 0x3, 0x60, 0x0, 0x86, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 0x6, 0xd6, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x84, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x14, 0x15, 0x80, 0x15, 0x61, 0x7, 0xae, 0x57, 0x50, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x60, 0x4, 0x60, 0x0, 0x86, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x54, 0x14, 0x15, 0x5b, 0x15, 0x61, 0x8, 0xc9, 0x57, 0x81, 0x60, 0x4, 0x60, 0x0, 0x86, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 0x8, 0x3e, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x81, 0x60, 0x4, 0x60, 0x0, 0x86, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x82, 0x82, 0x54, 0x3, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x5b, 0x81, 0x60, 0x3, 0x60, 0x0, 0x86, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x82, 0x82, 0x54, 0x3, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x81, 0x60, 0x3, 0x60, 0x0, 0x85, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x82, 0x82, 0x54, 0x1, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x82, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x84, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b, 0x69, 0xc2, 0xb0, 0x68, 0xfc, 0x37, 0x8d, 0xaa, 0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16, 0x28, 0xf5, 0x5a, 0x4d, 0xf5, 0x23, 0xb3, 0xef, 0x84, 0x60, 0x40, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xa3, 0x60, 0x1, 0x90, 0x50, 0x93, 0x92, 0x50, 0x50, 0x50, 0x56, 0x5b, 0x80, 0x60, 0x3, 0x60, 0x0, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 0xa, 0x21, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x80, 0x60, 0x3, 0x60, 0x0, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x82, 0x82, 0x54, 0x3, 0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x8, 0xfc, 0x82, 0x90, 0x81, 0x15, 0x2, 0x90, 0x60, 0x40, 0x51, 0x60, 0x0, 0x60, 0x40, 0x51, 0x80, 0x83, 0x3, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0xa, 0xae, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0x7f, 0xcf, 0x53, 0x2c, 0x15, 0xf0, 0xa6, 0xdb, 0xb, 0xd6, 0xd0, 0xe0, 0x38, 0xbe, 0xa7, 0x1d, 0x30, 0xd8, 0x8, 0xc7, 0xd9, 0x8c, 0xb3, 0xbf, 0x72, 0x68, 0xa9, 0x5b, 0xf5, 0x8, 0x1b, 0x65, 0x82, 0x60, 0x40, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xa2, 0x50, 0x56, 0x5b, 0x60, 0x2, 0x60, 0x0, 0x90, 0x54, 0x90, 0x61, 0x1, 0x0, 0xa, 0x90, 0x4, 0x60, 0xff, 0x16, 0x81, 0x56, 0x5b, 0x60, 0x3, 0x60, 0x20, 0x52, 0x80, 0x60, 0x0, 0x52, 0x60, 0x40, 0x60, 0x0, 0x20, 0x60, 0x0, 0x91, 0x50, 0x90, 0x50, 0x54, 0x81, 0x56, 0x5b, 0x60, 0x1, 0x80, 0x54, 0x60, 0x1, 0x81, 0x60, 0x1, 0x16, 0x15, 0x61, 0x1, 0x0, 0x2, 0x3, 0x16, 0x60, 0x2, 0x90, 0x4, 0x80, 0x60, 0x1f, 0x1, 0x60, 0x20, 0x80, 0x91, 0x4, 0x2, 0x60, 0x20, 0x1, 0x60, 0x40, 0x51, 0x90, 0x81, 0x1, 0x60, 0x40, 0x52, 0x80, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 0x60, 0x20, 0x1, 0x82, 0x80, 0x54, 0x60, 0x1, 0x81, 0x60, 0x1, 0x16, 0x15, 0x61, 0x1, 0x0, 0x2, 0x3, 0x16, 0x60, 0x2, 0x90, 0x4, 0x80, 0x15, 0x61, 0xb, 0xc0, 0x57, 0x80, 0x60, 0x1f, 0x10, 0x61, 0xb, 0x95, 0x57, 0x61, 0x1, 0x0, 0x80, 0x83, 0x54, 0x4, 0x2, 0x83, 0x52, 0x91, 0x60, 0x20, 0x1, 0x91, 0x61, 0xb, 0xc0, 0x56, 0x5b, 0x82, 0x1, 0x91, 0x90, 0x60, 0x0, 0x52, 0x60, 0x20, 0x60, 0x0, 0x20, 0x90, 0x5b, 0x81, 0x54, 0x81, 0x52, 0x90, 0x60, 0x1, 0x1, 0x90, 0x60, 0x20, 0x1, 0x80, 0x83, 0x11, 0x61, 0xb, 0xa3, 0x57, 0x82, 0x90, 0x3, 0x60, 0x1f, 0x16, 0x82, 0x1, 0x91, 0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x81, 0x56, 0x5b, 0x60, 0x0, 0x61, 0xb, 0xd5, 0x33, 0x84, 0x84, 0x61, 0x6, 0x86, 0x56, 0x5b, 0x90, 0x50, 0x92, 0x91, 0x50, 0x50, 0x56, 0x5b, 0x60, 0x4, 0x60, 0x20, 0x52, 0x81, 0x60, 0x0, 0x52, 0x60, 0x40, 0x60, 0x0, 0x20, 0x60, 0x20, 0x52, 0x80, 0x60, 0x0, 0x52, 0x60, 0x40, 0x60, 0x0, 0x20, 0x60, 0x0, 0x91, 0x50, 0x91, 0x50, 0x50, 0x54, 0x81, 0x56];

method {:verify false} block_0_0x0000(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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
	if st.PC() == 0xad { st := block_0_0x00ad(st); return st; }
	st := Push1(st,0x00);
	st := CallDataLoad(st);
	st := PushN(st,29,0x0100000000000000000000000000000000000000000000000000000000);
	st := Swap(st,1);
	st := Div(st);
	st := Push4(st,0xffffffff);
	st := And(st);
	st := Dup(st,1);
	st := Push4(st,0x06fdde03);
	st := Eq(st);
	st := Push1(st,0xb6);
	assume st.IsJumpDest(0xb6);
	st := JumpI(st);
	if st.PC() == 0xb6 { st := block_0_0x00b6(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0x095ea7b3);
	st := Eq(st);
	st := Push2(st,0x0141);
	assume st.IsJumpDest(0x141);
	st := JumpI(st);
	if st.PC() == 0x141 { st := block_0_0x0141(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0x18160ddd);
	st := Eq(st);
	st := Push2(st,0x019b);
	assume st.IsJumpDest(0x19b);
	st := JumpI(st);
	if st.PC() == 0x19b { st := block_0_0x019b(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0x23b872dd);
	st := Eq(st);
	st := Push2(st,0x01c4);
	assume st.IsJumpDest(0x1c4);
	st := JumpI(st);
	if st.PC() == 0x1c4 { st := block_0_0x01c4(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0x2e1a7d4d);
	st := Eq(st);
	st := Push2(st,0x023d);
	assume st.IsJumpDest(0x23d);
	st := JumpI(st);
	if st.PC() == 0x23d { st := block_0_0x023d(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0x313ce567);
	st := Eq(st);
	st := Push2(st,0x0260);
	assume st.IsJumpDest(0x260);
	st := JumpI(st);
	if st.PC() == 0x260 { st := block_0_0x0260(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0x70a08231);
	st := Eq(st);
	st := Push2(st,0x028f);
	assume st.IsJumpDest(0x28f);
	st := JumpI(st);
	if st.PC() == 0x28f { st := block_0_0x028f(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0x95d89b41);
	st := Eq(st);
	st := Push2(st,0x02dc);
	assume st.IsJumpDest(0x2dc);
	st := JumpI(st);
	if st.PC() == 0x2dc { st := block_0_0x02dc(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0xa9059cbb);
	st := Eq(st);
	st := Push2(st,0x036a);
	assume st.IsJumpDest(0x36a);
	st := JumpI(st);
	if st.PC() == 0x36a { st := block_0_0x036a(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0xd0e30db0);
	st := Eq(st);
	st := Push2(st,0x03c4);
	assume st.IsJumpDest(0x3c4);
	st := JumpI(st);
	if st.PC() == 0x3c4 { st := block_0_0x03c4(st); return st; }
	st := Dup(st,1);
	st := Push4(st,0xdd62ed3e);
	st := Eq(st);
	st := Push2(st,0x03ce);
	assume st.IsJumpDest(0x3ce);
	st := JumpI(st);
	if st.PC() == 0x3ce { st := block_0_0x03ce(st); return st; }
	st := block_0_0x00ad(st);
	return st;
}

method {:verify false} block_0_0x00ad(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x00ad
requires 0 <= st'.Operands() <= 1
{
	var st := st';
	st := JumpDest(st);
	st := Push1(st,0xb4);
	st := Push2(st,0x043a);
	assume st.IsJumpDest(0x43a);
	st := Jump(st);
	st := block_0_0x043a(st);
	return st;
}

method {:verify false} block_0_0x00b4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x00b4
requires 0 <= st'.Operands() <= 1
{
	var st := st';
	st := JumpDest(st);
	st := Stop(st);
	return st;
}

method {:verify false} block_0_0x00b6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x00c0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x00c7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x0141(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0141
requires st'.Operands() == 1
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

method {:verify false} block_0_0x014c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x014c
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := Push2(st,0x0181);
	st := Push1(st,0x04);
	st := Dup(st,1);
	st := Dup(st,1);
	st := CallDataLoad(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := Push2(st,0x0575);
	assume st.IsJumpDest(0x575);
	st := Jump(st);
	st := block_0_0x0575(st);
	return st;
}

method {:verify false} block_0_0x0181(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0181
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

method {:verify false} block_0_0x019b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x019b
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := CallValue(st);
	st := IsZero(st);
	st := Push2(st,0x01a6);
	assume st.IsJumpDest(0x1a6);
	st := JumpI(st);
	if st.PC() == 0x1a6 { st := block_0_0x01a6(st); return st; }
	st := Push1(st,0x00);
	st := Dup(st,1);
	st := Revert(st);
	return st;
}

method {:verify false} block_0_0x01a6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x01a6
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := Push2(st,0x01ae);
	st := Push2(st,0x0667);
	assume st.IsJumpDest(0x667);
	st := Jump(st);
	st := block_0_0x0667(st);
	return st;
}

method {:verify false} block_0_0x01ae(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x01ae
requires st'.Operands() == 2
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

method {:verify false} block_0_0x01c4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
	st := And(st);
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
	st := And(st);
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

method {:verify false} block_0_0x0223(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x023d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x023d
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := CallValue(st);
	st := IsZero(st);
	st := Push2(st,0x0248);
	assume st.IsJumpDest(0x248);
	st := JumpI(st);
	if st.PC() == 0x248 { st := block_0_0x0248(st); return st; }
	st := Push1(st,0x00);
	st := Dup(st,1);
	st := Revert(st);
	return st;
}

method {:verify false} block_0_0x0248(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0248
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := Push2(st,0x025e);
	st := Push1(st,0x04);
	st := Dup(st,1);
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
	st := Push2(st,0x09d3);
	assume st.IsJumpDest(0x9d3);
	st := Jump(st);
	st := block_0_0x09d3(st);
	return st;
}

method {:verify false} block_0_0x025e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x025e
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := Stop(st);
	return st;
}

method {:verify false} block_0_0x0260(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0260
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := CallValue(st);
	st := IsZero(st);
	st := Push2(st,0x026b);
	assume st.IsJumpDest(0x26b);
	st := JumpI(st);
	if st.PC() == 0x26b { st := block_0_0x026b(st); return st; }
	st := Push1(st,0x00);
	st := Dup(st,1);
	st := Revert(st);
	return st;
}

method {:verify false} block_0_0x026b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x026b
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := Push2(st,0x0273);
	st := Push2(st,0x0aff);
	assume st.IsJumpDest(0xaff);
	st := Jump(st);
	st := block_0_0x0aff(st);
	return st;
}

method {:verify false} block_0_0x0273(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0273
requires st'.Operands() == 3
requires (st'.Peek(1) == 0x273)
{
	var st := st';
	st := JumpDest(st);
	st := Push1(st,0x40);
	st := MLoad(st);
	st := Dup(st,1);
	st := Dup(st,3);
	st := Push1(st,0xff);
	st := And(st);
	st := Push1(st,0xff);
	st := And(st);
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

method {:verify false} block_0_0x028f(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x028f
requires st'.Operands() == 1
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

method {:verify false} block_0_0x029a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x029a
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := Push2(st,0x02c6);
	st := Push1(st,0x04);
	st := Dup(st,1);
	st := Dup(st,1);
	st := CallDataLoad(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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

method {:verify false} block_0_0x02c6(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x02c6
requires st'.Operands() == 3
requires (st'.Peek(1) == 0x2c6)
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

method {:verify false} block_0_0x02dc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x02e7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x02ef(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x036a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
	st := And(st);
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

method {:verify false} block_0_0x03aa(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x03c4(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x03c4
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := Push2(st,0x03cc);
	st := Push2(st,0x043a);
	assume st.IsJumpDest(0x43a);
	st := Jump(st);
	st := block_0_0x043a(st);
	return st;
}

method {:verify false} block_0_0x03cc(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x03cc
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := Stop(st);
	return st;
}

method {:verify false} block_0_0x03ce(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x03ce
requires st'.Operands() == 1
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

method {:verify false} block_0_0x03d9(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x03d9
requires st'.Operands() == 1
{
	var st := st';
	st := JumpDest(st);
	st := Push2(st,0x0424);
	st := Push1(st,0x04);
	st := Dup(st,1);
	st := Dup(st,1);
	st := CallDataLoad(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := And(st);
	st := Swap(st,1);
	st := Push1(st,0x20);
	assert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);
	st := Add(st);
	st := Swap(st,1);
	st := Swap(st,2);
	st := Swap(st,1);
	st := Pop(st);
	st := Pop(st);
	st := Push2(st,0x0bdd);
	assume st.IsJumpDest(0xbdd);
	st := Jump(st);
	st := block_0_0x0bdd(st);
	return st;
}

method {:verify false} block_0_0x0424(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0424
requires st'.Operands() == 3
requires (st'.Peek(1) == 0x424)
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

method {:verify false} block_0_0x043a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x043a
requires 1 <= st'.Operands() <= 2
requires (st'.Peek(0) == 0xb4) || (st'.Peek(0) == 0x3cc) || (st'.Peek(0) == 0xb4)
{
	var st := st';
	st := JumpDest(st);
	st := CallValue(st);
	st := Push1(st,0x03);
	st := Push1(st,0x00);
	st := Caller(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := Caller(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := PushN(st,32,0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c);
	st := CallValue(st);
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
	st := LogN(st,2);
	assume st.IsJumpDest(0xb4);
	assume st.IsJumpDest(0x3cc);
	assume st.IsJumpDest(0xb4);
	st := Jump(st);
	match st.PC() {
		case 0xb4 => { st := block_0_0x00b4(st); }
		case 0x3cc => { st := block_0_0x03cc(st); }
		case 0xb4 => { st := block_0_0x00b4(st); }
	}
	return st;
}

method {:verify false} block_0_0x04d7(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x056d(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x0575(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0575
requires st'.Operands() == 4
requires (st'.Peek(2) == 0x181)
{
	var st := st';
	st := JumpDest(st);
	st := Push1(st,0x00);
	st := Dup(st,2);
	st := Push1(st,0x04);
	st := Push1(st,0x00);
	st := Caller(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := Dup(st,6);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := Dup(st,2);
	st := Swap(st,1);
	st := SStore(st);
	st := Pop(st);
	st := Dup(st,3);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := Caller(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := PushN(st,32,0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
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
	st := Swap(st,3);
	st := Swap(st,2);
	st := Pop(st);
	st := Pop(st);
	assume st.IsJumpDest(0x181);
	st := Jump(st);
	st := block_0_0x0181(st);
	return st;
}

method {:verify false} block_0_0x0667(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0667
requires st'.Operands() == 2
requires (st'.Peek(0) == 0x1ae)
{
	var st := st';
	st := JumpDest(st);
	st := Push1(st,0x00);
	st := Address(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := Balance(st);
	st := Swap(st,1);
	st := Pop(st);
	st := Swap(st,1);
	assume st.IsJumpDest(0x1ae);
	st := Jump(st);
	st := block_0_0x01ae(st);
	return st;
}

method {:verify false} block_0_0x0686(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x06d6
requires 6 <= st'.Operands() <= 10
requires (st'.Peek(0) == 0x0)
requires (st'.Peek(4) == 0x223) || (st'.Peek(4) == 0xbd5)
{
	var st := st';
	st := JumpDest(st);
	st := Caller(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := Dup(st,5);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := And(st);
	st := Dup(st,5);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
		case 0xbd5 => { st := block_0_0x0bd5(st); }
	}
	return st;
}

method {:verify false} block_0_0x09d3(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x09d3
requires st'.Operands() == 3
requires (st'.Peek(1) == 0x25e)
{
	var st := st';
	st := JumpDest(st);
	st := Dup(st,1);
	st := Push1(st,0x03);
	st := Push1(st,0x00);
	st := Caller(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := Push2(st,0x0a21);
	assume st.IsJumpDest(0xa21);
	st := JumpI(st);
	if st.PC() == 0xa21 { st := block_0_0x0a21(st); return st; }
	st := Push1(st,0x00);
	st := Dup(st,1);
	st := Revert(st);
	return st;
}

method {:verify false} block_0_0x0a21(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0a21
requires st'.Operands() == 3
requires (st'.Peek(1) == 0x25e)
{
	var st := st';
	st := JumpDest(st);
	st := Dup(st,1);
	st := Push1(st,0x03);
	st := Push1(st,0x00);
	st := Caller(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
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
	st := Caller(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := Push2(st,0x08fc);
	st := Dup(st,3);
	st := Swap(st,1);
	st := Dup(st,2);
	st := IsZero(st);
	assert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);
	st := Mul(st);
	st := Swap(st,1);
	st := Push1(st,0x40);
	st := MLoad(st);
	st := Push1(st,0x00);
	st := Push1(st,0x40);
	st := MLoad(st);
	st := Dup(st,1);
	st := Dup(st,4);
	assert st.Peek(1) <= st.Peek(0);
	st := Sub(st);
	st := Dup(st,2);
	st := Dup(st,6);
	st := Dup(st,9);
	st := Dup(st,9);
	var CONTINUING(cc) := Call(st);
	{
		var inner := cc.CallEnter(1);
		if inner.EXECUTING? { inner := external_call(cc.sender,inner); }
		st := cc.CallReturn(inner);
	}
	st := Swap(st,4);
	st := Pop(st);
	st := Pop(st);
	st := Pop(st);
	st := Pop(st);
	st := IsZero(st);
	st := IsZero(st);
	st := Push2(st,0x0aae);
	assume st.IsJumpDest(0xaae);
	st := JumpI(st);
	if st.PC() == 0xaae { st := block_0_0x0aae(st); return st; }
	st := Push1(st,0x00);
	st := Dup(st,1);
	st := Revert(st);
	return st;
}

method {:verify false} block_0_0x0aae(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0aae
requires st'.Operands() == 3
requires (st'.Peek(1) == 0x25e)
{
	var st := st';
	st := JumpDest(st);
	st := Caller(st);
	st := PushN(st,20,0xffffffffffffffffffffffffffffffffffffffff);
	st := And(st);
	st := PushN(st,32,0x7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65);
	st := Dup(st,3);
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
	st := LogN(st,2);
	st := Pop(st);
	assume st.IsJumpDest(0x25e);
	st := Jump(st);
	st := block_0_0x025e(st);
	return st;
}

method {:verify false} block_0_0x0aff(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0aff
requires st'.Operands() == 2
requires (st'.Peek(0) == 0x273)
{
	var st := st';
	st := JumpDest(st);
	st := Push1(st,0x02);
	st := Push1(st,0x00);
	st := Swap(st,1);
	st := SLoad(st);
	st := Swap(st,1);
	st := Push2(st,0x0100);
	st := Exp(st);
	st := Swap(st,1);
	st := Div(st);
	st := Push1(st,0xff);
	st := And(st);
	st := Dup(st,2);
	assume st.IsJumpDest(0x273);
	st := Jump(st);
	st := block_0_0x0273(st);
	return st;
}

method {:verify false} block_0_0x0b12(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0b12
requires st'.Operands() == 3
requires (st'.Peek(1) == 0x2c6)
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

method {:verify false} block_0_0x0b2a(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x0bc0(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x0bc8(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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
	st := block_0_0x0686(st);
	return st;
}

method {:verify false} block_0_0x0bd5(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
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

method {:verify false} block_0_0x0bdd(st': EvmState.ExecutingState) returns (st'': EvmState.State)
requires st'.evm.code == Code.Create(BYTECODE_0);
requires st'.WritesPermitted() && st'.PC() == 0x0bdd
requires st'.Operands() == 4
requires (st'.Peek(2) == 0x424)
{
	var st := st';
	st := JumpDest(st);
	st := Push1(st,0x04);
	st := Push1(st,0x20);
	st := MStore(st);
	st := Dup(st,2);
	st := Push1(st,0x00);
	st := MStore(st);
	st := Push1(st,0x40);
	st := Push1(st,0x00);
	st := Keccak256(st);
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
	st := Swap(st,2);
	st := Pop(st);
	st := Pop(st);
	st := SLoad(st);
	st := Dup(st,2);
	assume st.IsJumpDest(0x424);
	st := Jump(st);
	st := block_0_0x0424(st);
	return st;
}

// 0x00a165627a7a72305820deb4c2ccab3c2fdca32ab3f46728389c2fe2c165d5fafa07661e4e004f6c344a0029
