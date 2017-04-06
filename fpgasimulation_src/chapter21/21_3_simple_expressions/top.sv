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
typedef enum {add_op, and_op, xor_op, mul_op,no_op,rst_op} operation_t;

class alu_operation;
   rand logic[7:0] A,B;
   rand operation_t op;
endclass


module top;
   alu_operation req;

initial begin
    $display ("---- A < 'h4 , B < 'hA ----");
    req = new();
    for (int i = 1; i<=5; i++) begin  
        assert(req.randomize() with { 
              A < 'h4;
              B < 'hA;
          });
        $display("A: %3h  B: %3h   SUM: %2h", req.A, req.B,req.A+req.B);
    end
    req = new();
    $display ("---- A + B == 8'hFF ----");
    for (int i = 1; i<=5; i++) begin

      assert(req.randomize() with { 
             A+B == 8'hFF;
          });
        $display("A: %3h  B: %3h   SUM: %2h", req.A, req.B,req.A+req.B);
    end
end // initial begin 
 
endmodule 


