import ovm_pkg::*;

module top;
 string m;
 initial begin
   $sformat(m,"%m");
   ovm_top.set_report_verbosity_level(200);
   ovm_top.ovm_report_info   (m,"Just Info",    300, `__FILE__,`__LINE__);
   ovm_top.ovm_report_warning(m,"A Warning!",   200, `__FILE__,`__LINE__);
   ovm_top.ovm_report_error  (m,"Normal Error", 100, `__FILE__,`__LINE__);
   ovm_top.ovm_report_fatal  (m,"Fatal Error" ,   0, `__FILE__,`__LINE__);
 end
endmodule

