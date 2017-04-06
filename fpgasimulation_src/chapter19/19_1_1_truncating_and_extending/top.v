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

   reg [7:0]  reg8;
   reg [63:0] reg64_ext, reg64_zero;
   integer    my_random, i, seed;

   initial
      begin
         seed = 5;
         for (i = 1; i<= 4; i=i+1) begin
            my_random = $random (seed);
            reg8       =  my_random;
            reg64_ext  =  my_random;
            reg64_zero = {my_random};
            $display;
            $display ("my_random(2's comp):  %d", my_random);
            $display ("my_random(hex     ):  %h",my_random);
            $display ("reg8:                 %h", reg8);
            $display ("reg64_ext:            %h", reg64_ext);
            $display ("reg64_zero:           %h",reg64_zero);
         end
      end
endmodule


