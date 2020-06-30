///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2018 Xilinx, Inc.
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
// /___/  \  /     Vendor      : Xilinx
// \   \   \/      Version     : 2018.3
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        OBUFDS_GTM
// /___/   /\      Filename    : OBUFDS_GTM.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps


`celldefine


module OBUFDS_GTM #(



  parameter [0:0] REFCLK_EN_TX_PATH = 1'b0,
  parameter integer REFCLK_ICNTL_TX = 0
)(
  output O,
  output OB,

  input CEB,
  input I
);

// define constants
  localparam MODULE_NAME = "OBUFDS_GTM";
  
  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [0:0] REFCLK_EN_TX_PATH_REG = REFCLK_EN_TX_PATH;
  reg [31:0] REFCLK_ICNTL_TX_REG = REFCLK_ICNTL_TX;





  reg [3:0] REFCLK_ICNTL_TX_BIN;






tri0 glblGSR = glbl.GSR;
tri0 glblGTS = glbl.GTS;



  reg attr_test;
  reg attr_err;
  
  initial begin
  trig_attr = 1'b0;
  


    attr_test = 1'b0;
  
    attr_err = 1'b0;
    #1;
    trig_attr = ~trig_attr;
  end






  always @ (trig_attr) begin
  #1;
  REFCLK_ICNTL_TX_BIN = REFCLK_ICNTL_TX_REG[3:0];
  
  end



  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((REFCLK_ICNTL_TX_REG != 0) &&
         (REFCLK_ICNTL_TX_REG != 1) &&
         (REFCLK_ICNTL_TX_REG != 3) &&
         (REFCLK_ICNTL_TX_REG != 7) &&
         (REFCLK_ICNTL_TX_REG != 15))) begin
      $display("Error: [Unisim %s-102] REFCLK_ICNTL_TX attribute is set to %d.  Legal values for this attribute are 0, 1, 3, 7 or 15. Instance: %m", MODULE_NAME, REFCLK_ICNTL_TX_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end


// begin behavioral model

// =====================
// Generate O
// =====================

  assign O = (~REFCLK_EN_TX_PATH_REG || (CEB === 1'b1) || glblGTS) ? 1'bz : I;
  assign OB = (~REFCLK_EN_TX_PATH_REG || (CEB === 1'b1) || glblGTS) ? 1'bz : ~I;











// end behavioral model

endmodule

`endcelldefine
