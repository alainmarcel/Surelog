// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: string_putc
:description: string.putc()  tests
:tags: 6.16.2
*/
module top();
	string a = "Test";
	initial
		a.putc(2, "B");
endmodule
