// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: implicit_external_constraint_0
:description: implicit external constraint test
:tags: 18.5.1
*/

class a;
    rand int b;
    constraint c;
endclass

constraint a::c { b == 0; }
