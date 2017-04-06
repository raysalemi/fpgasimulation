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
logic [7:0]   A,B;

covergroup op_cov;

   coverpoint op {
      bins single_cycle[] = {[add_op : xor_op], rst_op,no_op};
      bins multi_cycle = {mul_op};

      bins opn_rst[] = ([add_op:no_op] => rst_op);
      bins rst_opn[] = (rst_op => [add_op:no_op]);

      bins sngl_mul[] = ([add_op:xor_op],no_op => mul_op);
      bins mul_sngl[] = (mul_op => [add_op:xor_op], no_op);

      bins twoops[] = ([add_op:no_op] [* 2]);
      bins manymult = (mul_op [* 3:5]);

      bins rstmulrst   = (rst_op => mul_op [=  2] => rst_op);
      bins rstmulrstim = (rst_op => mul_op [-> 2] => rst_op);

      }

   A_00_FF: coverpoint A {
      bins zeros = { 0 };
      bins ones  = { 'hFF };
   }

   B_00_FF: coverpoint B {
      bins zero_or_ff[] = {0, 'hFF};
   }


endgroup

covergroup zeros_and_ones;

   all_ops : coverpoint op {
      ignore_bins null_ops = {rst_op, no_op};}


   a_leg: coverpoint A {
      bins zeros = {'h00};
      bins others= {['h01:'hFE]};
      bins ones  = {'hFF};}

   b_leg: coverpoint B {
      bins zeros = {'h00};
      bins others= {['h01:'hFE]};
      bins ones  = {'hFF};}

   basic : cross a_leg, b_leg, all_ops;

endgroup




op_cov oc;
zeros_and_ones c_00_FF;

string s, m;
  task run;
      oc = new();
      c_00_FF = new();
     req = new();
     repeat (50) begin
        assert(req.randomize());
        sample_req;
        $sformat(s,"Request: %s",req.convert2string);
        $sformat(m,"%m");
        ovm_top.ovm_report_info(m,s,300);
        op_f.put(req.clone());
     end
     #500;
     ovm_top.die();
 endtask // run

 task sample_req;
   A = req.A;
   B = req.B;
   op = req.op;
   oc.sample();
   c_00_FF.sample();
 endtask

endmodule

