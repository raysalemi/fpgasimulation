/*************************************************************************
   Copyright 2008 Ray Salemi

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
**************************************************************************/
`include "std_ovl_defines.h"

module alu_protocol_monitor (
      input clk,
      input reset_n,
      input start,
      input wire[2:0] op,
      input wire[7:0] A,B,
      input done,
      input wire[15:0] result);
  
   wire[`OVL_FIRE_WIDTH-1:0] ovl_fire;
    
   // Verification Assertions
   ovl_implication done_means_start
     (.clock(clk),
      .reset(reset_n),
      .enable (1'b1),
      .fire (ovl_fire),
      .antecedent_expr(done),
      .consequent_expr(start));

   ovl_next #(.num_cks(1)) no_done_on_nop 
     (.clock(clk),
      .reset(reset_n),
      .enable (1'b1),
      .fire (ovl_fire), 
      .start_event(start && (op == 3'b0)),
      .test_expr(!done));

   ovl_width #(.max_cks(1)) done_one_cycle
     (.clock(clk),
      .reset(reset_n),
      .enable (1'b1),
      .fire (ovl_fire),
      .test_expr(done));

endmodule