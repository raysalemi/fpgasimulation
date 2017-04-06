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
   randc operation_t op;
endclass

module top;

  alu_operation req;
  string msg;
  integer i;

  initial begin
     req = new();
     $display ("---- A inside {[0:8'h5], 8'hFF} ----");
     $display ("---- B inside {[8'h0A:8'h0F], [8'h01:8'h03], 8'hFE} ----");
     for (i = 1; i<=5; i++) begin
       assert(req.randomize() with {
           A inside {[0:8'h5],8'hFF};
           B inside {[8'h0A:8'h0F], [8'h01:8'h03], 8'hFE};
         });
       $display ("A: %2h  B:%2H", req.A,req.B);
     end // for (i=1; i<=5; i++);
     $display;
     $display ("---- A inside {[8'hFB:$]} ----");
     for (i = 1; i<=5; i++) begin
       assert(req.randomize() with {
          A inside {['hFB:$]};
       });
       $display ("A: %2h", req.A);
     end // for (i=1; i<=5; i++);

     $display;
     $display ("---- A + B inside {8'h10,8'hFF} ----");
     for (i = 1; i<=5; i++) begin
       assert( req.randomize()  with {
           (A + B) inside {8'h10,8'hFF};
         });
       $display ("A: %2h  B:%2h   A+B:%3h", req.A,req.B,req.A+req.B);
     end // for (i=1; i<=5; i++);
     $display;
     $display ("---- op  inside [add_op : xor_op] ----");
     for (i = 1; i<=6; i++) begin
        assert(req.randomize() with  {
             op inside {[add_op : xor_op]};
          });
          $display ("A: %2h  B:%2h   OP:%s", req.A,req.B,req.op);
      end
     $display;
     $display ("---- A  inside [`h10 : `h20] ----");
     $display ("----         A[0] == 0;      ----");
     for (i = 1; i<=6; i++) begin
        assert(req.randomize() with  {
             A inside {['h10 : 'h20]};
             A[0] == 0;
          });
          $display ("A: %2h", req.A);
      end

  end // initial
endmodule


