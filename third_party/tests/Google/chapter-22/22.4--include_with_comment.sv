// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.4--include_with_comment
:description: Test
:tags: 22.4
:type: preprocessing parsing
*/
`include "dummy_include.sv" // comments after `include are perfectly legal
module top ();
endmodule
