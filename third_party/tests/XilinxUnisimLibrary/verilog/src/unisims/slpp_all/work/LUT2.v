///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2016 Xilinx, Inc.
// 
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
///////////////////////////////////////////////////////////////////////////////
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor      : Xilinx
// \   \   \/     Version     : 2017.1
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                  2-Bit Look-Up Table
// /___/   /\     Filename : LUT2.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    03/23/04 - Initial version.
//    03/11/05 - Add LOC Parameter
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine
//    09/12/16 - ANSI ports, speed improvements
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps/1 ps


`celldefine


module LUT2 #(



  parameter [3:0] INIT = 4'h0
)(
  output O,

  input I0,
  input I1
);

// define constants
  localparam MODULE_NAME = "LUT2";

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only



  reg [3:0] INIT_REG = INIT;


  x_lut2_mux4 (O, INIT_REG[3], INIT_REG[2], INIT_REG[1], INIT_REG[0], I1, I0);









endmodule

`endcelldefine


primitive x_lut2_mux4 (o, d3, d2, d1, d0, s1, s0);

  output o;
  input d3, d2, d1, d0;
  input s1, s0;

  table

    // d3  d2  d1  d0  s1  s0 : o;

       ?   ?   ?   100 : 1;
       ?   ?   ?   000 : 0;
       ?   ?   1 ?   01 : 1;
       ?   ?   0 ?   01 : 0;
       ?   1 ?   ?   10 : 1;
       ?   0 ?   ?   10 : 0;
       1 ?   ?   ?   11 : 1;
       0 ?   ?   ?   11 : 0;

       ?   ?   000 x  : 0;
       ?   ?   110 x  : 1;
       00 ?   ?   1 x  : 0;
       11 ?   ?   1 x  : 1;

       ?   0 ?   0 x   0 : 0;
       ?   1 ?   1 x   0 : 1;
       0 ?   0 ?   x   1 : 0;
       1 ?   1 ?   x   1 : 1;

       0000 x   x  : 0;
       1111 x   x  : 1;

  endtable

endprimitive