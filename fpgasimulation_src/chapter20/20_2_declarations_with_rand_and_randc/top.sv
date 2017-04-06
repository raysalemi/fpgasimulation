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
class my_rand_obj;
   rand  logic [2:0] random;
   randc bit   [2:0] cyclic;
   randc enum {DOGS, CATS, TREES, FLOWERS} life;
   
endclass


module top;

   my_rand_obj r;
   
  initial 
   begin
      r = new();
      $display;
		$write("RAND  RANDOM: ");
      for (int i=0; i<=15; i++) begin
          assert(r.randomize());
          $write("%0d ",r.random);
          if (i == 7) $write ("| ");
      end
      $display;
		$write("RANDC CYCLIC: ");
		for (int i=0; i<=15; i++) begin
			 assert(r.randomize());
			 $write("%0d ",r.cyclic);
			 if (i == 7) $write ("| ");
		end
		$display;
		$write("RANDC LIFE: ");
		for (int i=0; i<=7; i++) begin
			 assert(r.randomize());
			 $write("%0s ",r.life);
			 if (i == 3) $write ("| ");
		end
	   $display;
   end
endmodule


         
       
