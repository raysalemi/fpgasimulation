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

   generator      tester    (.op_f(op_f));
   alu_predictor  predictor (.op_f(op_f), .res_f(res_f));
   result_printer printer   (             .res_f(res_f));

 initial begin
      ovm_top.set_report_verbosity_level(300);
      ovm_top.set_report_id_action(`OUTPUTID, OVM_NO_ACTION);
      op_f  = new("op_f");
      res_f = new("req_f");
      fork
         tester.run();
         predictor.run();
         printer.run();
      join_none
   end
endmodule

