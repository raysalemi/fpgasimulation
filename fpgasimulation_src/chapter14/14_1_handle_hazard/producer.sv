import ovm_pkg::*;
import tinyalu_pkg::*;

module producer (ref tlm_fifo #(alu_operation) fifo);

  alu_operation t;
  string m;

  task run;

    $sformat(m,"%m");

    // First transaction
    t = new (8'h00, 8'h00, add_op);
    ovm_top.ovm_report_info(m, {"WILL BE LOST: ",t.convert2string});
    fifo.put(t);

    // Second transaction
    t.A = 8'hFF;
    t.B = 8'h55;
    ovm_top.ovm_report_info(m, {"generated: ",t.convert2string});
    fifo.put(t);

    // Third transaction
    t.A = 8'hAA;
    t.B = 8'hEE;
    t.op = xor_op;
    ovm_top.ovm_report_info(m, {"generated: ",t.convert2string});
    fifo.put(t);
  endtask

endmodule


