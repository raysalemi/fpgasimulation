-suppress 2167

+incdir+../../ovm/src
../../ovm/src/ovm_pkg.sv

-sv 

+libext+.vlib
+libext+.v
+incdir+../../std_ovl
+define+OVL_ASSERT_ON+OVL_SVA
-y ../../std_ovl

tinyalu_pkg.sv
alu_driver.sv
alu_responder.sv
alu_firewall.sv
alu_predictor.sv
alu_comparator.sv
alu_protocol_monitor.sv
result_printer.sv
top.sv

