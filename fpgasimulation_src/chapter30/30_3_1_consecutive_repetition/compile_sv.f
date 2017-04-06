-suppress 2167

+incdir+../../ovm/src
../../ovm/src/ovm_pkg.sv

-sv 

+libext+.vlib
+libext+.v
+incdir+../../std_ovl
+define+OVL_ASSERT_ON
+define+OVL_COVER_ON
+define+OVL_SVA
+define+OVL_MAX_REPORT_COVER_POINT=0
-y ../../std_ovl

../../tinyalu_common/tinyalu_rst_pkg.sv
alu_driver.sv
alu_responder.sv
alu_firewall.sv
alu_predictor.sv
alu_comparator.sv
alu_protocol_monitor.sv
alu_functional_coverage.sv
result_printer.sv
top.sv

