setup_design -design threebitcounter
setup_design -search_path {../../std_ovl}
setup_design -defines { +define+OVL_VERILOG +define+OVL_SYNTHESIS}
setup_design -manufacturer Lattice -family LatticeSC -part LFSC3GA15E -speed 5 -package FPBGA256
add_input_file assertion.v
add_input_file threebitcounter.vhd
add_input_file ../../std_ovl/ovl_never.v
add_input_file ../../std_ovl/ovl_implication.v
compile

