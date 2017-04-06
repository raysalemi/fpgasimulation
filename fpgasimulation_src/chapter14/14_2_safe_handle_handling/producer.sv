import ovm_pkg::*;
import tinyalu_pkg::*;

module producer (ref tlm_fifo #(alu_operation) fifo);

  alu_operation t;
  string s;

  task run;

    $sformat(s,"%m");
    t = new (8'h00, 8'h00, add_op);
    ovm_top.ovm_report_info(s, {"generated: ",t.convert2string});
    fifo.put(t.clone);

    t.A = 8'hFF;
    t.B = 8'h55;
    ovm_top.ovm_report_info(s, {"generated: ",t.convert2string});
    fifo.put(t.clone);

    t.A = 8'hAA;
    t.B = 8'hEE;
    t.op = xor_op;
    ovm_top.ovm_report_info(s, {"generated: ",t.convert2string});
    fifo.put(t.clone);
  endtask
endmodule


