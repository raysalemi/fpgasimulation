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
class implication;
   rand bit flag;
   rand logic[3:0] value;
endclass

module top;
   implication imp;
   int flagcnt = 0;
   initial begin
     imp = new();
     for (int i = 1; i<=10; i++) begin
      assert (
         imp.randomize() with {
           flag -> (value == 0);
          });
      $display ("flag %b, value %h", imp.flag, imp.value);
      flagcnt = flagcnt + imp.flag;
     end
     $display ("flagcnt: %0d",flagcnt);
   end
endmodule // top

