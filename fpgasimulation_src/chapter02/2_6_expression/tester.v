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
// Module tiny_cache_lib.tester.struct
//
// Created:
//          by - rsalemi.UNKNOWN (MAW-RSALEMI-LT)
//          at - 15:17:24 11/ 1/2006
//
// Generated by Mentor Graphics' HDL Designer(TM) 2006.1 (Build 56) Beta
//


module tester( 
   clk, 
   cpuwait, 
   cpu_rd, 
   cpu_wr, 
   cpubus_address, 
   reset, 
   cpu_data
);


// Internal Declarations

input        clk;
input        cpuwait;
output       cpu_rd;
output       cpu_wr;
output [7:0] cpubus_address;
output       reset;
inout  [7:0] cpu_data;


wire        clk;
wire        cpuwait;
wire        cpu_rd;
wire        cpu_wr;
wire [7:0]  cpubus_address;
wire        reset;
wire [7:0]  cpu_data;

// Local declarations

// Internal signal declarations
wire [7:0] cpubus_data_reg;
wire       done;
wire       go;
wire       rst;
wire [1:0] transaction_req;


// Instances 
cpubus_sm cpubus_int( 
   .clk             (clk), 
   .cpuwait         (cpuwait), 
   .go              (go), 
   .rst             (rst), 
   .transaction_req (transaction_req), 
   .cpu_rd          (cpu_rd), 
   .cpu_wr          (cpu_wr), 
   .done            (done), 
   .reset           (reset)
); 

testrunner #(0,1,2,3) testprogram( 
   .cpubus_data_reg (cpubus_data_reg), 
   .transaction_req (transaction_req), 
   .go              (go), 
   .done            (done), 
   .cpubus_address  (cpubus_address), 
   .rst             (rst)
); 


// ModuleWare code(v1.8) for instance 'U_2' of 'tribuf'
assign cpu_data = (cpu_wr) ? cpubus_data_reg : {8'bz};

endmodule // tester

