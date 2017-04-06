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
class array_holder;
   rand logic [3:0] array [];

   task show;
      $display ("--- array.size() = %0d---",array.size());
      $write("index:\t");
      foreach(array[i]) $write("%6d",i);$display;
      $write("logic:\t");
      foreach(array[i]) $write("%6d",array[i]);$display;
   endtask // show

endclass

module top;
  array_holder ar;

  initial begin
     ar = new();
     for (int i = 1; i<=3; i++) begin
        assert(ar.randomize() with {
          array.size() > 0;
          array.size() < 10;
          foreach (array[x])
             if (x>0) array[x] > array[x-1];
          });
        ar.show;
     end
  end
endmodule

