include "../evm-dafny/src/dafny/evm.dfy"
include "../evm-dafny/src/dafny/state.dfy"

module Header {
	import opened Int
	import EvmState
	import opened Memory

	type u256 = Int.u256
	const MAX_U256 : nat := Int.MAX_U256

	const BYTECODE_0 : seq<u8> := [
		0x60, 0x60, 0x60, 0x40, 0x52, 0x60, 0x4, 0x36, 
		0x10, 0x61, 0x0, 0xaf, 0x57, 0x60, 0x0, 0x35, 
		0x7c, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 
		0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 
		0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 
		0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x90, 0x4, 
		0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x80, 0x63, 
		0x6, 0xfd, 0xde, 0x3, 0x14, 0x61, 0x0, 0xb9, 
		0x57, 0x80, 0x63, 0x9, 0x5e, 0xa7, 0xb3, 0x14, 
		0x61, 0x1, 0x47, 0x57, 0x80, 0x63, 0x18, 0x16, 
		0xd, 0xdd, 0x14, 0x61, 0x1, 0xa1, 0x57, 0x80, 
		0x63, 0x23, 0xb8, 0x72, 0xdd, 0x14, 0x61, 0x1, 
		0xca, 0x57, 0x80, 0x63, 0x2e, 0x1a, 0x7d, 0x4d, 
		0x14, 0x61, 0x2, 0x43, 0x57, 0x80, 0x63, 0x31, 
		0x3c, 0xe5, 0x67, 0x14, 0x61, 0x2, 0x66, 0x57, 
		0x80, 0x63, 0x70, 0xa0, 0x82, 0x31, 0x14, 0x61, 
		0x2, 0x95, 0x57, 0x80, 0x63, 0x95, 0xd8, 0x9b, 
		0x41, 0x14, 0x61, 0x2, 0xe2, 0x57, 0x80, 0x63, 
		0xa9, 0x5, 0x9c, 0xbb, 0x14, 0x61, 0x3, 0x70, 
		0x57, 0x80, 0x63, 0xd0, 0xe3, 0xd, 0xb0, 0x14, 
		0x61, 0x3, 0xca, 0x57, 0x80, 0x63, 0xdd, 0x62, 
		0xed, 0x3e, 0x14, 0x61, 0x3, 0xd4, 0x57, 0x5b, 
		0x61, 0x0, 0xb7, 0x61, 0x4, 0x40, 0x56, 0x5b, 
		0x0, 0x5b, 0x34, 0x15, 0x61, 0x0, 0xc4, 0x57, 
		0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x0, 0xcc, 
		0x61, 0x4, 0xdd, 0x56, 0x5b, 0x60, 0x40, 0x51, 
		0x80, 0x80, 0x60, 0x20, 0x1, 0x82, 0x81, 0x3, 
		0x82, 0x52, 0x83, 0x81, 0x81, 0x51, 0x81, 0x52, 
		0x60, 0x20, 0x1, 0x91, 0x50, 0x80, 0x51, 0x90, 
		0x60, 0x20, 0x1, 0x90, 0x80, 0x83, 0x83, 0x60, 
		0x0, 0x5b, 0x83, 0x81, 0x10, 0x15, 0x61, 0x1, 
		0xc, 0x57, 0x80, 0x82, 0x1, 0x51, 0x81, 0x84, 
		0x1, 0x52, 0x60, 0x20, 0x81, 0x1, 0x90, 0x50, 
		0x61, 0x0, 0xf1, 0x56, 0x5b, 0x50, 0x50, 0x50, 
		0x50, 0x90, 0x50, 0x90, 0x81, 0x1, 0x90, 0x60, 
		0x1f, 0x16, 0x80, 0x15, 0x61, 0x1, 0x39, 0x57, 
		0x80, 0x82, 0x3, 0x80, 0x51, 0x60, 0x1, 0x83, 
		0x60, 0x20, 0x3, 0x61, 0x1, 0x0, 0xa, 0x3, 
		0x19, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 
		0x50, 0x5b, 0x50, 0x92, 0x50, 0x50, 0x50, 0x60, 
		0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 
		0x34, 0x15, 0x61, 0x1, 0x52, 0x57, 0x60, 0x0, 
		0x80, 0xfd, 0x5b, 0x61, 0x1, 0x87, 0x60, 0x4, 
		0x80, 0x80, 0x35, 0x73, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 
		0x80, 0x35, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 
		0x90, 0x50, 0x50, 0x61, 0x5, 0x7b, 0x56, 0x5b, 
		0x60, 0x40, 0x51, 0x80, 0x82, 0x15, 0x15, 0x15, 
		0x15, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 
		0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 
		0xf3, 0x5b, 0x34, 0x15, 0x61, 0x1, 0xac, 0x57, 
		0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x1, 0xb4, 
		0x61, 0x6, 0x6d, 0x56, 0x5b, 0x60, 0x40, 0x51, 
		0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 
		0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 
		0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x1, 0xd5, 
		0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x2, 
		0x29, 0x60, 0x4, 0x80, 0x80, 0x35, 0x73, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 
		0x90, 0x91, 0x90, 0x80, 0x35, 0x73, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 
		0x91, 0x90, 0x80, 0x35, 0x90, 0x60, 0x20, 0x1, 
		0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0x6, 0x8c, 
		0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x15, 
		0x15, 0x15, 0x15, 0x81, 0x52, 0x60, 0x20, 0x1, 
		0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 
		0x3, 0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x2, 
		0x4e, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 
		0x2, 0x64, 0x60, 0x4, 0x80, 0x80, 0x35, 0x90, 
		0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x50, 0x50, 
		0x61, 0x9, 0xd9, 0x56, 0x5b, 0x0, 0x5b, 0x34, 
		0x15, 0x61, 0x2, 0x71, 0x57, 0x60, 0x0, 0x80, 
		0xfd, 0x5b, 0x61, 0x2, 0x79, 0x61, 0xb, 0x5, 
		0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x60, 
		0xff, 0x16, 0x60, 0xff, 0x16, 0x81, 0x52, 0x60, 
		0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 
		0x80, 0x91, 0x3, 0x90, 0xf3, 0x5b, 0x34, 0x15, 
		0x61, 0x2, 0xa0, 0x57, 0x60, 0x0, 0x80, 0xfd, 
		0x5b, 0x61, 0x2, 0xcc, 0x60, 0x4, 0x80, 0x80, 
		0x35, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 
		0x60, 0x20, 0x1, 0x90, 0x91, 0x90, 0x50, 0x50, 
		0x61, 0xb, 0x18, 0x56, 0x5b, 0x60, 0x40, 0x51, 
		0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 
		0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 
		0x90, 0xf3, 0x5b, 0x34, 0x15, 0x61, 0x2, 0xed, 
		0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 0x61, 0x2, 
		0xf5, 0x61, 0xb, 0x30, 0x56, 0x5b, 0x60, 0x40, 
		0x51, 0x80, 0x80, 0x60, 0x20, 0x1, 0x82, 0x81, 
		0x3, 0x82, 0x52, 0x83, 0x81, 0x81, 0x51, 0x81, 
		0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x80, 0x51, 
		0x90, 0x60, 0x20, 0x1, 0x90, 0x80, 0x83, 0x83, 
		0x60, 0x0, 0x5b, 0x83, 0x81, 0x10, 0x15, 0x61, 
		0x3, 0x35, 0x57, 0x80, 0x82, 0x1, 0x51, 0x81, 
		0x84, 0x1, 0x52, 0x60, 0x20, 0x81, 0x1, 0x90, 
		0x50, 0x61, 0x3, 0x1a, 0x56, 0x5b, 0x50, 0x50, 
		0x50, 0x50, 0x90, 0x50, 0x90, 0x81, 0x1, 0x90, 
		0x60, 0x1f, 0x16, 0x80, 0x15, 0x61, 0x3, 0x62, 
		0x57, 0x80, 0x82, 0x3, 0x80, 0x51, 0x60, 0x1, 
		0x83, 0x60, 0x20, 0x3, 0x61, 0x1, 0x0, 0xa, 
		0x3, 0x19, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 
		0x91, 0x50, 0x5b, 0x50, 0x92, 0x50, 0x50, 0x50, 
		0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 
		0x5b, 0x34, 0x15, 0x61, 0x3, 0x7b, 0x57, 0x60, 
		0x0, 0x80, 0xfd, 0x5b, 0x61, 0x3, 0xb0, 0x60, 
		0x4, 0x80, 0x80, 0x35, 0x73, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0x16, 0x90, 0x60, 0x20, 0x1, 0x90, 0x91, 
		0x90, 0x80, 0x35, 0x90, 0x60, 0x20, 0x1, 0x90, 
		0x91, 0x90, 0x50, 0x50, 0x61, 0xb, 0xce, 0x56, 
		0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 0x15, 0x15, 
		0x15, 0x15, 0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 
		0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 
		0x90, 0xf3, 0x5b, 0x61, 0x3, 0xd2, 0x61, 0x4, 
		0x40, 0x56, 0x5b, 0x0, 0x5b, 0x34, 0x15, 0x61, 
		0x3, 0xdf, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 
		0x61, 0x4, 0x2a, 0x60, 0x4, 0x80, 0x80, 0x35, 
		0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 
		0x20, 0x1, 0x90, 0x91, 0x90, 0x80, 0x35, 0x73, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0x16, 0x90, 0x60, 0x20, 
		0x1, 0x90, 0x91, 0x90, 0x50, 0x50, 0x61, 0xb, 
		0xe3, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x80, 0x82, 
		0x81, 0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 
		0x60, 0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xf3, 
		0x5b, 0x34, 0x60, 0x3, 0x60, 0x0, 0x33, 0x73, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 
		0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 
		0x20, 0x60, 0x0, 0x82, 0x82, 0x54, 0x1, 0x92, 
		0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x33, 0x73, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0xe1, 0xff, 
		0xfc, 0xc4, 0x92, 0x3d, 0x4, 0xb5, 0x59, 0xf4, 
		0xd2, 0x9a, 0x8b, 0xfc, 0x6c, 0xda, 0x4, 0xeb, 
		0x5b, 0xd, 0x3c, 0x46, 0x7, 0x51, 0xc2, 0x40, 
		0x2c, 0x5c, 0x5c, 0xc9, 0x10, 0x9c, 0x34, 0x60, 
		0x40, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 
		0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 
		0x91, 0x3, 0x90, 0xa2, 0x56, 0x5b, 0x60, 0x0, 
		0x80, 0x54, 0x60, 0x1, 0x81, 0x60, 0x1, 0x16, 
		0x15, 0x61, 0x1, 0x0, 0x2, 0x3, 0x16, 0x60, 
		0x2, 0x90, 0x4, 0x80, 0x60, 0x1f, 0x1, 0x60, 
		0x20, 0x80, 0x91, 0x4, 0x2, 0x60, 0x20, 0x1, 
		0x60, 0x40, 0x51, 0x90, 0x81, 0x1, 0x60, 0x40, 
		0x52, 0x80, 0x92, 0x91, 0x90, 0x81, 0x81, 0x52, 
		0x60, 0x20, 0x1, 0x82, 0x80, 0x54, 0x60, 0x1, 
		0x81, 0x60, 0x1, 0x16, 0x15, 0x61, 0x1, 0x0, 
		0x2, 0x3, 0x16, 0x60, 0x2, 0x90, 0x4, 0x80, 
		0x15, 0x61, 0x5, 0x73, 0x57, 0x80, 0x60, 0x1f, 
		0x10, 0x61, 0x5, 0x48, 0x57, 0x61, 0x1, 0x0, 
		0x80, 0x83, 0x54, 0x4, 0x2, 0x83, 0x52, 0x91, 
		0x60, 0x20, 0x1, 0x91, 0x61, 0x5, 0x73, 0x56, 
		0x5b, 0x82, 0x1, 0x91, 0x90, 0x60, 0x0, 0x52, 
		0x60, 0x20, 0x60, 0x0, 0x20, 0x90, 0x5b, 0x81, 
		0x54, 0x81, 0x52, 0x90, 0x60, 0x1, 0x1, 0x90, 
		0x60, 0x20, 0x1, 0x80, 0x83, 0x11, 0x61, 0x5, 
		0x56, 0x57, 0x82, 0x90, 0x3, 0x60, 0x1f, 0x16, 
		0x82, 0x1, 0x91, 0x5b, 0x50, 0x50, 0x50, 0x50, 
		0x50, 0x81, 0x56, 0x5b, 0x60, 0x0, 0x81, 0x60, 
		0x4, 0x60, 0x0, 0x33, 0x73, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 
		0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 
		0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 
		0x85, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 
		0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 
		0x60, 0x0, 0x20, 0x81, 0x90, 0x55, 0x50, 0x82, 
		0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x33, 0x73, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0x8c, 0x5b, 
		0xe1, 0xe5, 0xeb, 0xec, 0x7d, 0x5b, 0xd1, 0x4f, 
		0x71, 0x42, 0x7d, 0x1e, 0x84, 0xf3, 0xdd, 0x3, 
		0x14, 0xc0, 0xf7, 0xb2, 0x29, 0x1e, 0x5b, 0x20, 
		0xa, 0xc8, 0xc7, 0xc3, 0xb9, 0x25, 0x84, 0x60, 
		0x40, 0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 
		0x1, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 
		0x91, 0x3, 0x90, 0xa3, 0x60, 0x1, 0x90, 0x50, 
		0x92, 0x91, 0x50, 0x50, 0x56, 0x5b, 0x60, 0x0, 
		0x30, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x31, 
		0x90, 0x50, 0x90, 0x56, 0x5b, 0x60, 0x0, 0x81, 
		0x60, 0x3, 0x60, 0x0, 0x86, 0x73, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 
		0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x54, 
		0x10, 0x15, 0x15, 0x15, 0x61, 0x6, 0xdc, 0x57, 
		0x60, 0x0, 0x80, 0xfd, 0x5b, 0x33, 0x73, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0x16, 0x84, 0x73, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0x16, 0x14, 0x15, 0x80, 0x15, 0x61, 
		0x7, 0xb4, 0x57, 0x50, 0x7f, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0x60, 0x4, 0x60, 
		0x0, 0x86, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 
		0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 
		0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 
		0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x33, 0x73, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 
		0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 
		0x20, 0x54, 0x14, 0x15, 0x5b, 0x15, 0x61, 0x8, 
		0xcf, 0x57, 0x81, 0x60, 0x4, 0x60, 0x0, 0x86, 
		0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 
		0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 
		0x0, 0x20, 0x60, 0x0, 0x33, 0x73, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 
		0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 0x54, 
		0x10, 0x15, 0x15, 0x15, 0x61, 0x8, 0x44, 0x57, 
		0x60, 0x0, 0x80, 0xfd, 0x5b, 0x81, 0x60, 0x4, 
		0x60, 0x0, 0x86, 0x73, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 
		0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 
		0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x33, 
		0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 
		0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 
		0x0, 0x20, 0x60, 0x0, 0x82, 0x82, 0x54, 0x3, 
		0x92, 0x50, 0x50, 0x81, 0x90, 0x55, 0x50, 0x5b, 
		0x81, 0x60, 0x3, 0x60, 0x0, 0x86, 0x73, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 
		0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 
		0x60, 0x0, 0x82, 0x82, 0x54, 0x3, 0x92, 0x50, 
		0x50, 0x81, 0x90, 0x55, 0x50, 0x81, 0x60, 0x3, 
		0x60, 0x0, 0x85, 0x73, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 
		0x52, 0x60, 0x20, 0x1, 0x90, 0x81, 0x52, 0x60, 
		0x20, 0x1, 0x60, 0x0, 0x20, 0x60, 0x0, 0x82, 
		0x82, 0x54, 0x1, 0x92, 0x50, 0x50, 0x81, 0x90, 
		0x55, 0x50, 0x82, 0x73, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0x16, 0x84, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 
		0x7f, 0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 
		0x9b, 0x69, 0xc2, 0xb0, 0x68, 0xfc, 0x37, 0x8d, 
		0xaa, 0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 
		0x16, 0x28, 0xf5, 0x5a, 0x4d, 0xf5, 0x23, 0xb3, 
		0xef, 0x84, 0x60, 0x40, 0x51, 0x80, 0x82, 0x81, 
		0x52, 0x60, 0x20, 0x1, 0x91, 0x50, 0x50, 0x60, 
		0x40, 0x51, 0x80, 0x91, 0x3, 0x90, 0xa3, 0x60, 
		0x1, 0x90, 0x50, 0x93, 0x92, 0x50, 0x50, 0x50, 
		0x56, 0x5b, 0x80, 0x60, 0x3, 0x60, 0x0, 0x33, 
		0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 
		0x1, 0x90, 0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 
		0x0, 0x20, 0x54, 0x10, 0x15, 0x15, 0x15, 0x61, 
		0xa, 0x27, 0x57, 0x60, 0x0, 0x80, 0xfd, 0x5b, 
		0x80, 0x60, 0x3, 0x60, 0x0, 0x33, 0x73, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x1, 0x90, 
		0x81, 0x52, 0x60, 0x20, 0x1, 0x60, 0x0, 0x20, 
		0x60, 0x0, 0x82, 0x82, 0x54, 0x3, 0x92, 0x50, 
		0x50, 0x81, 0x90, 0x55, 0x50, 0x33, 0x73, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0x16, 0x61, 0x8, 0xfc, 0x82, 
		0x90, 0x81, 0x15, 0x2, 0x90, 0x60, 0x40, 0x51, 
		0x60, 0x0, 0x60, 0x40, 0x51, 0x80, 0x83, 0x3, 
		0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 
		0x50, 0x50, 0x15, 0x15, 0x61, 0xa, 0xb4, 0x57, 
		0x60, 0x0, 0x80, 0xfd, 0x5b, 0x33, 0x73, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xff, 0xff, 0xff, 0x16, 0x7f, 0x7f, 0xcf, 0x53, 
		0x2c, 0x15, 0xf0, 0xa6, 0xdb, 0xb, 0xd6, 0xd0, 
		0xe0, 0x38, 0xbe, 0xa7, 0x1d, 0x30, 0xd8, 0x8, 
		0xc7, 0xd9, 0x8c, 0xb3, 0xbf, 0x72, 0x68, 0xa9, 
		0x5b, 0xf5, 0x8, 0x1b, 0x65, 0x82, 0x60, 0x40, 
		0x51, 0x80, 0x82, 0x81, 0x52, 0x60, 0x20, 0x1, 
		0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 
		0x3, 0x90, 0xa2, 0x50, 0x56, 0x5b, 0x60, 0x2, 
		0x60, 0x0, 0x90, 0x54, 0x90, 0x61, 0x1, 0x0, 
		0xa, 0x90, 0x4, 0x60, 0xff, 0x16, 0x81, 0x56, 
		0x5b, 0x60, 0x3, 0x60, 0x20, 0x52, 0x80, 0x60, 
		0x0, 0x52, 0x60, 0x40, 0x60, 0x0, 0x20, 0x60, 
		0x0, 0x91, 0x50, 0x90, 0x50, 0x54, 0x81, 0x56, 
		0x5b, 0x60, 0x1, 0x80, 0x54, 0x60, 0x1, 0x81, 
		0x60, 0x1, 0x16, 0x15, 0x61, 0x1, 0x0, 0x2, 
		0x3, 0x16, 0x60, 0x2, 0x90, 0x4, 0x80, 0x60, 
		0x1f, 0x1, 0x60, 0x20, 0x80, 0x91, 0x4, 0x2, 
		0x60, 0x20, 0x1, 0x60, 0x40, 0x51, 0x90, 0x81, 
		0x1, 0x60, 0x40, 0x52, 0x80, 0x92, 0x91, 0x90, 
		0x81, 0x81, 0x52, 0x60, 0x20, 0x1, 0x82, 0x80, 
		0x54, 0x60, 0x1, 0x81, 0x60, 0x1, 0x16, 0x15, 
		0x61, 0x1, 0x0, 0x2, 0x3, 0x16, 0x60, 0x2, 
		0x90, 0x4, 0x80, 0x15, 0x61, 0xb, 0xc6, 0x57, 
		0x80, 0x60, 0x1f, 0x10, 0x61, 0xb, 0x9b, 0x57, 
		0x61, 0x1, 0x0, 0x80, 0x83, 0x54, 0x4, 0x2, 
		0x83, 0x52, 0x91, 0x60, 0x20, 0x1, 0x91, 0x61, 
		0xb, 0xc6, 0x56, 0x5b, 0x82, 0x1, 0x91, 0x90, 
		0x60, 0x0, 0x52, 0x60, 0x20, 0x60, 0x0, 0x20, 
		0x90, 0x5b, 0x81, 0x54, 0x81, 0x52, 0x90, 0x60, 
		0x1, 0x1, 0x90, 0x60, 0x20, 0x1, 0x80, 0x83, 
		0x11, 0x61, 0xb, 0xa9, 0x57, 0x82, 0x90, 0x3, 
		0x60, 0x1f, 0x16, 0x82, 0x1, 0x91, 0x5b, 0x50, 
		0x50, 0x50, 0x50, 0x50, 0x81, 0x56, 0x5b, 0x60, 
		0x0, 0x61, 0xb, 0xdb, 0x33, 0x84, 0x84, 0x61, 
		0x6, 0x8c, 0x56, 0x5b, 0x90, 0x50, 0x92, 0x91, 
		0x50, 0x50, 0x56, 0x5b, 0x60, 0x4, 0x60, 0x20, 
		0x52, 0x81, 0x60, 0x0, 0x52, 0x60, 0x40, 0x60, 
		0x0, 0x20, 0x60, 0x20, 0x52, 0x80, 0x60, 0x0, 
		0x52, 0x60, 0x40, 0x60, 0x0, 0x20, 0x60, 0x0, 
		0x91, 0x50, 0x91, 0x50, 0x50, 0x54, 0x81, 0x56
	]
	method external_call(sender: u160, st: EvmState.ExecutingState) returns (r:EvmState.TerminatedState)
	ensures r.RETURNS? ==> r.world.Exists(sender) {
		return EvmState.ERROR(EvmState.INSUFFICIENT_GAS); // dummy
	}
/**
 * Alternative to Bytecode.And for masking u256 into a u1
 */
function AndU1(st: EvmState.ExecutingState): (st': EvmState.State)
requires st.Operands() >= 2 && st.Peek(0) == 1 {
    var rhs := st.Peek(1);
    var res := rhs % 2;
    st.Pop(2).Push(res).Next()
}
/**
 * Alternative to Bytecode.And for masking u256 into a u5
 */
function AndU5(st: EvmState.ExecutingState): (st': EvmState.State)
requires st.Operands() >= 2 && st.Peek(0) == 31 {
    var rhs := st.Peek(1);
    var res := rhs % 32;
    st.Pop(2).Push(res).Next()
}
/**
 * Alternative to Bytecode.And for masking u256 into a u8
 */
function AndU8(st: EvmState.ExecutingState): (st': EvmState.State)
requires st.Operands() >= 2 && st.Peek(0) == (Int.MAX_U8 as u256) {
    var rhs := st.Peek(1);
    var res := rhs % (Int.TWO_8 as u256);
    st.Pop(2).Push(res).Next()
}
/**
 * Alternative to Bytecode.And for masking u256 into a u32
 */
function AndU32(st: EvmState.ExecutingState): (st': EvmState.State)
requires st.Operands() >= 2 && st.Peek(0) == (Int.MAX_U32 as u256) {
    var rhs := st.Peek(1);
    var res := rhs % (Int.TWO_32 as u256);
    st.Pop(2).Push(res).Next()
}
/**
 * Alternative to Bytecode.And for masking u256 into a u64
 */
function AndU64(st: EvmState.ExecutingState): (st': EvmState.State)
requires st.Operands() >= 2 && st.Peek(0) == (Int.MAX_U64 as u256) {
    var rhs := st.Peek(1);
    var res := rhs % (Int.TWO_64 as u256);
    st.Pop(2).Push(res).Next()
}
/**
 * Alternative to Bytecode.And for masking u256 into a u128
 */
function AndU128(st: EvmState.ExecutingState): (st': EvmState.State)
requires st.Operands() >= 2 && st.Peek(0) == (Int.MAX_U128 as u256) {
    var rhs := st.Peek(1);
    var res := rhs % (Int.TWO_128 as u256);
    st.Pop(2).Push(res).Next()
}
/**
 * Alternative to Bytecode.And for masking u256 into a u160
 */
function AndU160(st: EvmState.ExecutingState): (st': EvmState.State)
requires st.Operands() >= 2 && st.Peek(0) == (Int.MAX_U160 as u256) {
    var rhs := st.Peek(1);
    var res := rhs % (Int.TWO_160 as u256);
    st.Pop(2).Push(res).Next()
}

/**
 * Alternative to Bytecode.And for masking upper 4 bytes of u256 
 * where the lower 28 bytes are zero
 */
function AndUpper4Bytes(st: EvmState.ExecutingState): (st': EvmState.State)
requires st.Operands() >= 2 
requires st.Peek(0) == 0xffffffff00000000000000000000000000000000000000000000000000000000 
requires st.Peek(1) % 0x100000000000000000000000000000000000000000000000000000000 == 0{
    var rhs := st.Peek(1);
    var res := rhs;
    st.Pop(2).Push(res).Next()
}

/**
 * Alternative to Bytecode.And for masking upper 13 bytes of u256 
 * where the lower 18 bytes are zero
 */
function AndUpper13Bytes(st: EvmState.ExecutingState): (st': EvmState.State)
requires st.Operands() >= 2 
requires st.Peek(0) == 0xffffffffffffffffffffffffff00000000000000000000000000000000000000 
requires st.Peek(1) % 0x100000000000000000000000000000000000000 == 0{
    var rhs := st.Peek(1);
    var res := rhs;
    st.Pop(2).Push(res).Next()
}

lemma {:axiom} TotalSupplyBoundAxiom(a: u256, b: u256)
	ensures (a as nat + b as nat) <= Int.MAX_U256 

function Hash(a: u256, b: u256): (h: u256)

lemma {:axiom} HashEquivalenceAxiom(st: EvmState.ExecutingState, h: u256, a: u256, b:u256)
	requires st.MemSize() >= 0x40 && h == st.evm.precompiled.Sha3(Memory.Slice(st.evm.memory, 0x00, 0x40))
	requires st.Read(0x00) == a && st.Read(0x20) == b
	ensures h == Hash(a,b)

lemma {:axiom} MemoryReadAxiom(st: EvmState.ExecutingState, i:nat)
	requires st.MemSize() >= i + 0x20 
	ensures Memory.Slice(st.evm.memory, i, 0x20) == Int.ToBytes(st.Read(i) as nat)

lemma {:axiom} NoCollisionsAxiom(h1: u256, h2: u256)
	ensures h1 != h2

lemma stackLemma(st: EvmState.ExecutingState, n: nat)
	requires 1 <= n <= 16 && st.Operands() == n
	ensures n == 1 ==> st.evm.stack.contents == [st.Peek(0)]
	ensures n == 2 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1)]
	ensures n == 3 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2)]
	ensures n == 4 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3)]
	ensures n == 5 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4)]
	ensures n == 6 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5)]
	ensures n == 7 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6)]
	ensures n == 8 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6),st.Peek(7)]
	ensures n == 9 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6),st.Peek(7),st.Peek(8)]
	ensures n == 10 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6),st.Peek(7),st.Peek(8),st.Peek(9)]
	ensures n == 11 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6),st.Peek(7),st.Peek(8),st.Peek(9),st.Peek(10)]
	ensures n == 12 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6),st.Peek(7),st.Peek(8),st.Peek(9),st.Peek(10),st.Peek(11)]
	ensures n == 13 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6),st.Peek(7),st.Peek(8),st.Peek(9),st.Peek(10),st.Peek(11),st.Peek(12)]
	ensures n == 14 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6),st.Peek(7),st.Peek(8),st.Peek(9),st.Peek(10),st.Peek(11),st.Peek(12),st.Peek(13)]
	ensures n == 15 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6),st.Peek(7),st.Peek(8),st.Peek(9),st.Peek(10),st.Peek(11),st.Peek(12),st.Peek(13),st.Peek(14)]
	ensures n == 16 ==> st.evm.stack.contents == [st.Peek(0),st.Peek(1),st.Peek(2),st.Peek(3),st.Peek(4),st.Peek(5),st.Peek(6),st.Peek(7),st.Peek(8),st.Peek(9),st.Peek(10),st.Peek(11),st.Peek(12),st.Peek(13),st.Peek(14),st.Peek(15)]

{}


}

