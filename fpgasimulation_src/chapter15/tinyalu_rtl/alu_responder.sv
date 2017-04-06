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


module alu_responder (ref tlm_fifo #(alu_result) res_f,
  input bit clk,
  input bit reset_n,
  input bit done,
  input logic [15:0] result);

  alu_result rslt;
  string m;

  initial $sformat (m,"%m");

  always @(posedge clk)
     if (done && reset_n) begin
       rslt = new (result);
       assert (res_f.try_put(rslt)) else
         ovm_top.ovm_report_fatal(m,"res_f is full",0,`__FILE__,`__LINE__);
       end
  endmodule



