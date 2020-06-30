///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2015 Xilinx, Inc.
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
// \   \   \/     Version     : 2015.3
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                       IDELAYE3/ODELAYE3 Tap Delay Value Control
// /___/   /\     Filename    : IDELAYCTRL.v
// \   \  /  \
//  \___\/\___\
//
// Revision:
//    03/23/04 - Initial version.
//    03/11/05 - Added LOC parameter and initialized outpus.
//    04/10/07 - CR 436682 fix, disable activity when rst is high
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    06/01/15 - 850338 - Added SIM_DEVICE and warning
// End Revision

`timescale 1 ps / 1 ps
 

`celldefine


module IDELAYCTRL #(



  parameter SIM_DEVICE = "7SERIES"
)(
  output RDY,

  input REFCLK,
  input RST
);

// define constants
  localparam MODULE_NAME = "IDELAYCTRL";

// Parameter encodings and registers
  localparam SIM_DEVICE_7SERIES = 0;
  localparam SIM_DEVICE_ULTRASCALE = 1;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
//`ifdef XIL_DR
//  `include "IDELAYCTRL_dr.v"
//`else
  localparam [80:1] SIM_DEVICE_REG = SIM_DEVICE;
//`endif




  reg attr_test = 1'b0;

  reg attr_err = 1'b0;

  reg RDY_out = 0;

  wire REFCLK_in;
  wire RST_in;






  assign RDY = RDY_out;





  assign REFCLK_in = REFCLK;
  assign RST_in = RST;


    time clock_edge;
    reg [63:0] period;
    reg clock_low, clock_high;
    reg clock_posedge, clock_negedge;
    reg lost;
    reg msg_flag = 1'b0;


  initial begin
    #1;
    trig_attr = ~trig_attr;
  end
  
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "7SERIES") &&
         (SIM_DEVICE_REG != "ULTRASCALE"))) begin
      $display("Error: [Unisim %s-104] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are 7SERIES or ULTRASCALE. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end


    always @(RST_in, lost) begin

   if (RST_in == 1'b1) begin
     RDY_out <= 1'b0;
   end else if (lost == 1)
     RDY_out <= 1'b0;
   else if (RST_in == 1'b0 && lost == 0)
     RDY_out <= 1'b1;
    end
   
   always @(posedge RST_in) begin
     if (SIM_DEVICE_REG == "ULTRASCALE" && msg_flag == 1'b0) begin 
       $display("Info: [Unisim %s-1] RST simulation behaviour for SIM_DEVICE %s may not match hardware behaviour when I/ODELAY DELAY_FORMAT = TIME if SelectIO User Guide recommendation for I/ODELAY connections or reset sequence are not followed. For more information, refer to the Select IO Userguide. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      msg_flag <= 1'b1;
     end
   end
    initial begin
   clock_edge <= 0;
   clock_high <= 0;
   clock_low <= 0;
   lost <= 1;
   period <= 0;
    end


    always @(posedge REFCLK_in) begin
      if(RST_in == 1'b0) begin
   clock_edge <= $time;
   if (period != 0 && (($time - clock_edge) <= (1.5 * period)))
       period <= $time - clock_edge;
   else if (period != 0 && (($time - clock_edge) > (1.5 * period)))
       period <= 0;
   else if ((period == 0) && (clock_edge != 0))
       period <= $time - clock_edge;
      end
    end
    
    always @(posedge REFCLK_in) begin
   clock_low <= 1'b0;
   clock_high <= 1'b1;
   if (period != 0)
       lost <= 1'b0;
   clock_posedge <= 1'b0;
   #((period * 9.1) / 10)
   if ((clock_low != 1'b1) && (clock_posedge != 1'b1))
       lost <= 1;
    end
    
    always @(posedge REFCLK_in) begin
   clock_negedge <= 1'b1;
    end
    
    always @(negedge REFCLK_in) begin
   clock_posedge <= 1'b1;
    end
    
    always @(negedge REFCLK_in) begin
   clock_high  <= 1'b0;
   clock_low   <= 1'b1;
   if (period != 0)
       lost <= 1'b0;
   clock_negedge <= 1'b0;
   #((period * 9.1) / 10)
   if ((clock_high != 1'b1) && (clock_negedge != 1'b1))
       lost <= 1;
    end

//*** Timing Checks Start here




  specify
  (RST => RDY) = (0:0:0, 0:0:0);
  (posedge RST => (RDY +: 0)) = (0:0:0, 0:0:0);
  (REFCLK => RDY) = (100:100:100, 100:100:100);










    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
