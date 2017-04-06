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

class test_request extends alu_operation;

  `include "test_constraint.svh"

endclass

module alu_tester(ref tlm_fifo #(alu_operation) op_f);

test_request req;
operation_t   op;

covergroup op_cov;
   coverpoint op;
endgroup

op_cov oc;

string s, m;
  task run;
      oc = new();

     req = new();
     repeat (1000) begin
        assert(req.randomize());
        op = req.op;
        oc.sample();
        $sformat(s,"Request: %s",req.convert2string);
        $sformat(m,"%m");
        ovm_top.ovm_report_info(m,s,300);
        op_f.put(req.clone());
     end
     #500;
     ovm_top.die();
 endtask // run
endmodule

