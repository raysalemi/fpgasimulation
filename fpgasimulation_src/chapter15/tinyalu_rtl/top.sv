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
   tlm_fifo #(alu_operation) op_f;
   tlm_fifo #(alu_result)    res_f;
   wire clk;
   wire reset_n;
   wire done;
   wire start;
   wire [2:0] op;
   wire [7:0] A;
   wire [7:0] B;
   wire [15:0] result;

   generator      tester     (.op_f(op_f));

   alu_driver driver
     (.op_f(op_f),
      .clk(clk),
      .reset_n(reset_n),
      .start(start),
      .done (done),
      .op(op),
      .A(A),
      .B(B));

   tinyalu RTLDUT
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

   result_printer printer   (.res_f(res_f));

 initial begin
      integer output_mcd;
      string m;
      $sformat(m,"%m");
      assert((output_mcd = $fopen(`OUTPUTFILENAME))) else
        ovm_top.ovm_report_fatal(m,
                {"Could not open ", `OUTPUTFILENAME},
                0,`__FILE__, `__LINE__);
      ovm_top.set_report_verbosity_level(0);
      ovm_top.set_report_id_file  (`OUTPUTID, output_mcd);
      ovm_top.set_report_id_action(`OUTPUTID, OVM_LOG);
      op_f  = new("op_f");
      res_f = new("req_f");
      fork
         tester.run();
         printer.run();
      join_none
   end
endmodule

