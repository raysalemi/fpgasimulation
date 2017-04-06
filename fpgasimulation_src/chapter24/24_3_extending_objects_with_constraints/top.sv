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
class number;
  rand logic [7:0] num;
endclass

class even_number extends number;
  constraint zerobit {num[0] == 0;}
endclass

class odd_number extends number;
  constraint oddbit {num[0] == 1;}
endclass

class fourdiv extends even_number;
  constraint zerobit1 {num[1] == 0;}
endclass

class prime_number extends odd_number;
  constraint prime_number {
      num inside {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,
      59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,
      139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,
      227,229,233,239,241,251};
            }
endclass

module top;
   number       n = new;
   even_number  e = new;
   odd_number   o = new;
   fourdiv      f = new;
   prime_number p = new;

   initial begin
      $display("Three sets of Numbers...");
      repeat (3) begin
        assert(n.randomize());
        assert(e.randomize());
        assert(o.randomize());
        assert(f.randomize());
        assert(p.randomize());

        $display("n: %3d,  e: %3d, o: %3d, f: %3d, p: %3d",
                  n.num, e.num, o.num, f.num, p.num);
      end
   end
endmodule



