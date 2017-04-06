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
`include "std_ovl_defines.h"

module alu_functional_coverage
  ( input bit clk,
    input bit reset_n,
    input bit done,
    input bit start,
    input logic [2:0] op,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [15:0] result);

    wire [2:0] fire;

    ovl_width #(.min_cks(1), .max_cks(4),
                .property_type(`OVL_IGNORE),
                .coverage_level(`OVL_COVER_BASIC | `OVL_COVER_CORNER))

       multi_clock(.clock(clk), .reset(reset_n), .enable (reset_n),
                   .fire(fire),
                   .test_expr(start));
endmodule

