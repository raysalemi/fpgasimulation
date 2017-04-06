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

module good_threads;

tlm_fifo #(int) fifo;

task producer;
  int data;
  for (data = 0; data<=5; data++) begin
     fifo.put(data);
     $display("Put Data: %d",data);
  end
endtask // producer

task consumer;
  int data;
  forever begin
    fifo.get(data);
    $display("Get Data: %d",data);
  end
endtask // consumer

initial begin
  fifo = new("fifo");
  fork
    producer;
    consumer;
  join_none
 end

endmodule

