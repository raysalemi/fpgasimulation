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
module alu_firewall(
	input [7:0] A,
	input [7:0] B,
	input clk,
	input done,
	input [2:0] op,
	input reset_n,
	input start);
	
	
	wire [2:0] fire;
	
	ovl_win_unchange #(.width(19)) no_data_op_change (
		.clock(clk),
		.reset(reset_n),
		.enable(1'b1),
		.fire(fire),
		.start_event(start && op),
		.test_expr({op, A, B}),
		.end_event(done));
	
	ovl_next clear_start (
		.clock(~clk),
		.reset(reset_n),
		.enable(1'b1),
		.fire(fire),
		.start_event(start && done),
		.test_expr(~(start || done)));
		
	ovl_implication done_only_if_start (
		.clock(clk),
		.reset(reset_n),
		.enable(1'b1),
		.fire(fire),
		.antecedent_expr(done),
		.consequent_expr(start));
endmodule
