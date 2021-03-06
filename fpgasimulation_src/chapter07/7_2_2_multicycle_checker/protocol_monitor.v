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

module protocol_monitor(
   input clk,
   input reset_n,
   input req,
   input ack);

  wire [`OVL_FIRE_WIDTH-1:0] fire;

  ovl_handshake
    #(.min_ack_cycle (2),.max_ack_cycle(4))
    check_ack
    (
       // Unique ports on ovl_handshake
     .req(req), .ack(ack),

       // Common ports on all OVL
     .clock(clk), .reset(reset_n), .enable(1'b1), .fire(fire));

 endmodule


