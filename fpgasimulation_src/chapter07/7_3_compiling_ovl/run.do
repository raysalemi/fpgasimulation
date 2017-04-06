if [file exists work] {vdel -all}
vlib work
vlog top.v -f compile.f
vcom threebitcounter.vhd
vsim top;
run -all


