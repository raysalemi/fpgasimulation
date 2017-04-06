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
typedef enum {baseball, football, hockey, basketball, lacrosse} sports;

class activity;
   rand sports sport;
endclass

module top;
   parameter total=10000;
   activity play=new();
   real bbcount;
   initial begin
    bbcount = 0;



    $display ("---- {baseball:= 1, football:=1, hockey:=1, basketball:=1} ----");
    for (int i = 1; i<=total; i++) begin
   assert(
      play.randomize() with {
       sport dist {baseball:= 1, football:=1, hockey:=1, basketball:=1};
     });
     if (play.sport == baseball) bbcount++;
    end
    $display ("We played baseball %0d of %0d times (%4.2f %%)",bbcount,total, bbcount/total*100.0);
    bbcount = 0;



    $display ("---- {baseball:= 3, football:=1, hockey:=1, basketball:=1} ----");
    for (int i = 1; i<=total; i++) begin
   assert(
      play.randomize() with {
       sport dist {baseball:= 3, football:=1, hockey:=1, basketball:=1};
     });
     if (play.sport == baseball) bbcount++;
     end
    $display ("We played baseball %0d of %0d times (%4.2f %%)",bbcount,total, bbcount/total*100.0);



     $display ("---- {baseball:= 3, [football:basketball]:=1} ----");
     bbcount = 0;
     for (int i = 1; i<=total; i++) begin
      assert(
         play.randomize() with {
             sport dist {baseball:= 3, [football:basketball]:=1};
      });
      if (play.sport == baseball) bbcount++;
      end
    $display ("We played baseball %0d of %0d times (%4.2f %%)",bbcount,total, bbcount/total*100.0);

     bbcount = 0;



     $display ("---- {baseball:= 3, [football:lacrosse]:=1} ----");
     for (int i = 1; i<=total; i++) begin
      assert(
         play.randomize() with {
             sport dist {baseball:= 3, [football:lacrosse]:=1};
      });
      if (play.sport == baseball) bbcount++;
      end
    $display ("We played baseball %0d of %0d times (%4.2f %%)",bbcount,total, bbcount/total*100.0);



     $display ("---- {baseball:= 1, [football:lacrosse]:/1} ----");
     bbcount = 0;
     for (int i = 1; i<=total; i++) begin
      assert(
         play.randomize() with {
             sport dist {baseball:= 1, [football:lacrosse]:/1};
      });
      if (play.sport == baseball) bbcount++;
      end
    $display ("We played baseball %0d of %0d times (%4.2f %%)",bbcount,total, bbcount/total*100.0);
   end // initial begin
endmodule // req_reader

