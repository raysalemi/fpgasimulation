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
typedef enum {baseball, football, hockey, basketball, lacrosse,
              tennis, soccer, rugby, badmitten, tabletennis,
              skating, running} sports;
typedef enum {rain, sun} summer_weather;

class activity;
   rand sports sport;
   rand summer_weather weather;
endclass

module top;
   parameter total=100;
   activity play=new();
   initial begin
     $display ("---- (weather == rain) -> (sport != baseball); ----");
     for (int i = 1; i<=10; i++) begin
	   assert(
		   play.randomize() with { 
		    (weather == rain) -> (sport != baseball);
         });
         $display("Weather: %6s  Sport: %s",play.weather, play.sport);
      end
    end // initial begin  
endmodule 

