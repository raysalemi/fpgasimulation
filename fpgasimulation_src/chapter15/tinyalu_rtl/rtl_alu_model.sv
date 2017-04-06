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
import ovm_pkg::*;
import tinyalu_pkg::*;

module rtl_alu_model (  ref tlm_fifo #(alu_operation) op_f,
		     ref tlm_fifo #(alu_result)    res_f);
   
   wire clk;
   wire reset_n;
   wire start;
   wire done;
   wire [2:0] op;
   wire [7:0] A;
   wire [7:0] B;
   wire [15:0] result;
   wire [2:0] ovl_fire;

   task run;
      // empty run task here for consistency.
   endtask // run
   
   alu_driver driver 
     (.op_f(op_f),
      .clk(clk),
      .reset_n(reset_n),
      .start(start),
      .done (done),
      .op(op),
      .A(A),
      .B(B));
 
   tinyalu DUT 
     (.clk(clk),
      .reset_n(reset_n),
      .start(start),
      .op(op),
      .A(A),
      .B(B),
      .done (done),
      .result(result));
   
   alu_responder responder
     (.res_f(res_f),
      .clk(clk),
      .reset_n(reset_n),
      .done(done),
      .result(result));

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
   
endmodule // rtl_alu_model
