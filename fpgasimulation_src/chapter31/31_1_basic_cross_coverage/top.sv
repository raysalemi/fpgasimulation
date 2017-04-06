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
typedef enum { roger, hui, marion} campers_t;
typedef enum {apple, pear, banana, trailMix} snacks_t;

class camperSnack;
  randc campers_t camper;
  rand  snacks_t snack;
endclass

module top;
  campers_t camper;
  snacks_t  snack;

  covergroup clipboard;
    coverpoint camper;
    coverpoint snack;
    matrix : cross camper, snack;
  endgroup

  initial begin
    clipboard cb = new();
    camperSnack snacktime = new();
    repeat ( 5 * camper.num()) begin
      assert(snacktime.randomize);
      camper = snacktime.camper;
      snack  = snacktime.snack;
      cb.sample();
    end
  end
endmodule


