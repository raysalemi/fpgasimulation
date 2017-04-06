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
//
// Include file ch2
//
// Created:
//          by - Ray.UNKNOWN (OFFICE)
//          at - 15:05:52 07/28/2007
//
// using Mentor Graphics HDL Designer(TM) 2006.1 (Build 72)
//
// synopsys template
// ### Please start your Verilog code here ###
// synopsys template
parameter NOTHING = 0,
READ    = 1,
WRITE   = 2,
RESET   = 3;

// Internal Declarations

output [7:0] cpubus_data_reg;
output [1:0] transaction_req;
output       go;
input        done;
output [7:0] cpubus_address;
output       rst;


reg [7:0] 	cpubus_data_reg;
reg [1:0] 	transaction_req;
reg 		go;
wire 	done;
reg [7:0] 	cpubus_address;
reg [6:0]  seed1, seed2;
reg 		rst;
integer 	i;
integer 	hstream,htrans;

task read;
  input [7:0] req_addr;
  
  begin
    $display ("---- READ  ----");
    $display ("Address: %h", req_addr);
    transaction_req = READ;
    cpubus_address = req_addr;
    go = 1;
    @(posedge done);
    go = 0;
    transaction_req = NOTHING;
  end
endtask

task write;
  input [7:0] req_addr;
  input [7:0] req_data;
  
  begin
    $display ("---- WRITE ----");
    $display ("Address: %h", req_addr);
    $display ("Data:    %h", req_data);
    transaction_req = WRITE;
    cpubus_address = req_addr;
    cpubus_data_reg = req_data;
    go = 1;
    @(posedge done);
    go = 0;
    transaction_req = NOTHING;
  end
endtask

task reset;
  begin
    $display ("---- RESET ----");
    transaction_req = RESET;
    go = 1;
    @(posedge done);
    go = 0;
    transaction_req = NOTHING;
  end
endtask


task rand;
  begin
    $display ("---- RAND  ----");
    transaction_req = {$random} % 2 + 1;
    seed1 = $random;
    seed2 = $random;
    cpubus_address = seed1 + seed2;
    cpubus_data_reg = $random;
    go = 1;
    @(posedge done);
    go = 0;
    transaction_req = NOTHING;
  end
endtask


