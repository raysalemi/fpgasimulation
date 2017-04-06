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
module petlove;
   parameter pet = "animals";
   parameter color = "all";
   initial
      $display("I love %s %s",color, pet);
endmodule

module top;
   petlove #(.pet("dogs"))                 U_dogs();
   petlove #(.color("brown"))              U_brown();
   petlove #(.pet("cats"),.color("black")) U_cats();
endmodule


