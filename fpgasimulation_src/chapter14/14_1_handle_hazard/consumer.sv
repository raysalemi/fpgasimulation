import ovm_pkg::*;
import tinyalu_pkg::*;

module consumer(ref tlm_fifo #(alu_operation) fifo);

  alu_operation t;
  string m;
  task run;
    $sformat(m, "%m");
    forever begin
      #10;
      fifo.get(t);
      ovm_top.ovm_report_info(m,{"Received: ", t.convert2string,"\n"});
    end
  endtask
endmodule

