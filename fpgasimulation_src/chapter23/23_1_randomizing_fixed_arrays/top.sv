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

typedef enum {red, grn, blu} color_t;
class color_frame;
   rand  logic [3:0] brightness [1023:0];
   rand  color_t     color [1023:0];

   task show;
      $display ("--- frame arrays from 9 to 21---");
      $write("index: ");
      for (int i=9;i<=21;i++) $write("%4d",i);$display;
      $write("brght: ");
      for (int i=9;i<=21;i++) $write("%4d",brightness[i]);$display;
      $write("color: ");
      for (int i=9;i<=21;i++) $write("%4s",color[i]);$display;
   endtask // displayarray
endclass



module top;
  color_frame frame;

  initial begin
     frame = new();
     for (int i = 1; i<=3; i++) begin
        assert(frame.randomize() with {
         foreach (brightness[x]) {
           if ((x%10) == 0) brightness[x] == 0;
           if ((x%10) != 0) brightness[x] > brightness[x-1];
           if ((x%10) != 0) color[x] == color[x-1];
           }}
        );
        frame.show;
     end
  end
endmodule

