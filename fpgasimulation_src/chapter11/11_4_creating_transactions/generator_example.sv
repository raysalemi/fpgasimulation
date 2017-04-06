import tinyalu_pkg::*;

module top;

   alu_operation op;

   initial begin
      op = new();
      $display("Default:      ",op.convert2string());
      op = new(8'h00,8'h01,add_op);
      $display("Initialized:  ",op.convert2string());
      op = new();
      assert(op.randomize());
      $display("Random:       ",op.convert2string());
      op = new();
      assert(op.randomize());
      $display("Random again: ",op.convert2string());
   end
endmodule // generate_and_print


