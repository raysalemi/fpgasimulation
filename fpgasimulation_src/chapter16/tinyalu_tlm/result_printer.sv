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

module result_printer(ref tlm_fifo #(alu_result) res_f);

   alu_result restran;
   string     filename;
   string     m;
   integer    file_handle;

   task run;
      $sformat(m,"%m");
      forever begin
         res_f.get(restran);
         ovm_top.ovm_report_info(m,
               restran.convert2string(),300);
         ovm_top.ovm_report_info(`OUTPUTID,
               restran.convert2string(),  0);
       end
   endtask
endmodule


