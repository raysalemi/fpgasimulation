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
   
   function void pre_randomize();
      $display (" ** randomizing **");
   endfunction
   
   function void print;
      $display ("random: ",random);
      $display ("cyclic: ",cyclic);
      $display ("life: %s"  ,life);
      $display;
   endfunction
      
   
endclass


module top;

   my_rand_obj r;
   
  initial 
   begin
      r = new();
      assert(r.randomize());
      r.print;
      
      $display ("call: r.rand_mode(0);");
      r.rand_mode(0);
      $display ("r.rand_mode.random() -> %0b ",r.random.rand_mode());
      $display ("r.rand_mode.cyclic() -> %0b ",r.cyclic.rand_mode());
      $display ("r.rand_mode.life()   -> %0b,",r.life.rand_mode());     
      assert(r.randomize());
      r.print();
      
      $display ("call: r.random.rand_mode(1);");
      $display ("call: r.life.rand_mode(1);"); 
      r.random.rand_mode(1);
      r.life.rand_mode(1);
      $display ("r.rand_mode.random() -> %0b ",r.random.rand_mode());
      $display ("r.rand_mode.cyclic() -> %0b ",r.cyclic.rand_mode());
      $display ("r.rand_mode.life()   -> %0b,",r.life.rand_mode());
      assert(r.randomize());
      r.print();
    end     
endmodule


         
       
