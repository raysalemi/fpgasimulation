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
`include  "tinyalu_defines.svh"

module alu_driver (
    ref tlm_fifo #(alu_operation) op_f,
    ref tlm_fifo #(alu_operation) pred_f,
    output bit clk,
    output bit reset_n,
    input  bit done,
    output bit start,
    output logic [2:0] op,
    output logic [7:0] A,
    output logic [7:0] B);

   alu_operation request;
   string m = "";

   initial $sformat(m,"%m");

   initial begin : clockgen
      clk = 0;
      forever #10 clk = ~clk;
   end

   task reset_alu;
      reset_n = 0;
      @(posedge clk);
      @(negedge clk);
      reset_n = 1;
   endtask

   initial reset_alu;

   always @(negedge clk) begin : drive_transactions
     if (!reset_n) begin : handle_reset
       start = 1'b0;
     end else
       if (!start) begin : start_operation
          if (op_f.try_get(request)) begin : new_transaction
            assert (pred_f.try_put(request)) else
              ovm_top.ovm_report_fatal(m,"pred_f is full",0,`__FILE__,`__LINE__);
            ovm_top.ovm_report_info(m,        request.convert2string(),500);
            ovm_top.ovm_report_info(`OUTPUTID,request.convert2string(),  0);
            if (request.op == rst_op)
              reset_alu;
            else begin
              op = request.op2bits();
              A = request.A;
              B = request.B;
              start = 1'b1;
            end
          end
        end
      else begin : in_operation
        if (done || (op == 3'b000)) begin : end_operation

          start = 0;
          wait_rand_clocks;
        end
      end
    end

   task wait_rand_clocks;
      logic [1:0] waittime;
      waittime = $random;
      repeat (waittime) @(posedge clk);
   endtask
endmodule


