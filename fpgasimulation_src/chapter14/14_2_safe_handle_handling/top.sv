import ovm_pkg::*;
import tinyalu_pkg::*;

module top;
  
  tlm_fifo #(alu_operation) fifo;
  
  producer tester  (fifo);
  consumer printer (fifo);
  
  initial
    begin
      ovm_top.set_report_verbosity_level(10000);
      fifo = new("fifo");
      fork 
        tester.run();
        printer.run();
      join_none
    end

endmodule
        
  