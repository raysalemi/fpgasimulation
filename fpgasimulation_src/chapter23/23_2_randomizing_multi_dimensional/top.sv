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
`define Y_MAX 4
`define X_MAX 3
class two_dim;
  rand logic [4:0]  my_2d[1:`X_MAX][1:`Y_MAX];

  task show;
    integer x,y;
    $display;
    $write ("   ");
    for (y = 1; y<= `Y_MAX; y++) $write("%2d ",y);$display;
    $write ("   ");
    for (y = 1; y<= `Y_MAX; y++) $write("-- ");$display;

    for (x = 1; x<=`X_MAX; x++)
     begin
      $write("%1d: ",x);
      for (y = 1; y<=`Y_MAX; y++)
          $write("%2d ",my_2d[x][y]);
      $display;
     end;
   endtask;

endclass;



module top;

   two_dim t;

   initial
     begin
       t = new();
       repeat (2) begin
          assert(t.randomize with {
             foreach(my_2d[x,y]) {
                if (x>1) my_2d[x][y] > my_2d[x-1][y];
                if (y>1) my_2d[x][y] > my_2d[x][y-1];
                if (y==1 && x > 1)
                         my_2d[x][y] > my_2d[x-1][`Y_MAX];
             }});
          t.show;
       end
     end
endmodule


