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

module generator(ref tlm_fifo #(alu_operation) op_f);

alu_operation op;

  task run;
      op = new (8'hFF, 8'h01, add_op);
      op_f.put(op);
      op = new (8'hFE, 8'h03, mul_op);
      op_f.put(op);
      op = new (8'h55, 8'hFF, and_op);
      op_f.put(op);
      op = new (8'h55, 8'hFF, xor_op);
      op_f.put(op);
      op = new();
      for (int i = 1; i<=10; i++) begin
         assert(op.randomize());
         ovm_top.ovm_report_info("random before",op.convert2string,400); 
         op_f.put(op.clone());
         ovm_top.ovm_report_info("random after",op.convert2string,400);
      end
      #500;
      ovm_top.die();
 endtask // run
endmodule

