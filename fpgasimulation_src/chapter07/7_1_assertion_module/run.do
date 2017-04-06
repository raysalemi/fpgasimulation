if [file exists work] {vdel -all}
vlib work
vlog top.v assertion.v -sv
vcom threebitcounter.vhd
vsim top;
run -all
