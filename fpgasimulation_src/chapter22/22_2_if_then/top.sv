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
typedef enum {jan, feb, mar, apr, may, jun, jul, aug, sep, oct, nov, dec} 
  month_t;

class date;
   rand integer year;
   rand month_t month;
   rand integer day;
endclass // implication_test

module top;
   date d;
   initial
     for (int i = 1; i<=10; i++) begin
		d = new();
		assert (
			d.randomize() with {
			  solve year,month before day;
			  day >0;
			  year > 2000; // avoid the div by 400 non-leap year
			  year <= 2050;
			  if (month inside {jan, mar, may, jul, aug,oct,dec})
			     day <= 31;
			  if (month == feb) 
				   if (year % 4 == 0) 
				      day <= 29;
			      else
			         day <= 28;
			  if (month inside {sep, apr, jun, nov})
			     day <= 30;
			  });
			     
			$display("%s %2d, %4d",d.month, d.day, d.year); 
			     
     end
endmodule // top

	