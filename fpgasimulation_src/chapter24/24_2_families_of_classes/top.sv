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
class memory_read;
  logic [15:0] read_data;
endclass

class cache_read extends memory_read;
  bit cache_hit;
endclass

module top;
  cache_read c;

  initial begin
    c = new();
    c.read_data = 'hF5;
    c.cache_hit = 1'b1;
  end

endmodule

