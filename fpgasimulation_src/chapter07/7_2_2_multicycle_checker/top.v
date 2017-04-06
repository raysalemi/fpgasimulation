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

module top;

   wire ack;
   wire req;
   reg clk;
   reg reset_n;

   req_ack DUT (.clk(clk),
                .reset_n(reset_n),
                .req(req),.ack(ack));

   req_ack_tester TESTER (.clk(clk),
                          .reset_n(reset_n),
                          .req(req),
                          .ack(ack));

   protocol_monitor pmon
       (.clk(clk), .reset_n(reset_n),
        .req(req), .ack(ack));

  initial begin
      reset_n = 0;
      clk = 0;
      @(posedge clk);
      @(negedge clk);
      reset_n = 1;
  end

  always #10 clk = ~clk;

endmodule

