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
module assertion (input clk, input rst, input ld, input inc,
                 input [2:0] data_in, input [2:0] data_out);

wire [`OVL_FIRE_WIDTH-1:0] fire;

ovl_never

#(.reset_polarity(`OVL_ACTIVE_HIGH), .msg ("Counter Overflow"))

U_counter_overflow

         // Common ports
         (.clock(clk), .reset(rst), .enable(~rst), .fire(fire),

         // ovl_never port
         .test_expr((data_out == 3'h7) && inc));

endmodule

