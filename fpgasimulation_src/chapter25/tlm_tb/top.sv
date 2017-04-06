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
import    ovm_pkg::*;
import    tinyalu_pkg::*;
`include  "tinyalu_defines.svh"

module top;
   tlm_fifo #(alu_operation) tst2drv_f;
   tlm_fifo #(alu_result)    res2prt_f;
   tlm_fifo #(alu_operation) drv2prd_f;
   tlm_fifo #(alu_result)    prd2cmp_f;
   tlm_fifo #(alu_result)    res2cmp_f;

   wire clk, reset_n, done, start;
   wire [2:0] op;
   wire [7:0] A,B;
   wire [15:0] result;

   alu_tester tester     (.op_f(tst2drv_f));

   alu_driver driver
     (.op_f(tst2drv_f),.pred_f(drv2prd_f),
      .clk(clk), .reset_n(reset_n),.start(start),.done (done),
      .op(op),.A(A),.B(B));

   tinyalu RTLDUT
     (.clk(clk),.reset_n(reset_n),.start(start),.op(op),.A(A),.B(B),
      .done (done),.result(result));

   alu_responder responder
     (.res_f(res2prt_f),.comp_f(res2cmp_f),
      .clk(clk),.reset_n(reset_n), .done(done),.result(result));

   result_printer printer   (.res_f(res2prt_f));

   alu_predictor  predictor (.op_f (drv2prd_f), .res_f(prd2cmp_f));

   alu_comparator comparator    (.predicted_f(prd2cmp_f),.actual_f(res2cmp_f));

 initial begin
      ovm_top.set_report_verbosity_level(200);
      ovm_top.set_report_max_quit_count(2);
      ovm_top.set_report_id_action(`OUTPUTID, OVM_NO_ACTION);

      tst2drv_f = new("tst2drv_f");
      res2prt_f = new("req_f");
      drv2prd_f = new("drv2prd_f");
      prd2cmp_f = new("prd2cmp_f");
      res2cmp_f = new("res2cmp_f");

      fork
         tester.run();
         predictor.run();
         comparator.run();
         printer.run();
      join_none
   end
endmodule

