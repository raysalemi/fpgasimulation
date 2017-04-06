import ovm_pkg::*;

module top;

 initial begin
   integer err_mcd;
   err_mcd = $fopen("errors.txt");
   ovm_top.set_report_verbosity_level(1000);
   ovm_top.set_report_severity_id_action(OVM_ERROR, "TOP", OVM_LOG);
   ovm_top.set_report_severity_id_file  (OVM_ERROR, "TOP", err_mcd);
   ovm_top.dump_report_state();

   ovm_top.ovm_report_info("TOP", "This won't go in a file", 300);
   ovm_top.ovm_report_error("TOP", "This will only go in a file",300);
   ovm_top.ovm_report_error("NOTTOP", "This won't go in a file either",300);

   $fclose(err_mcd);
 end
endmodule

