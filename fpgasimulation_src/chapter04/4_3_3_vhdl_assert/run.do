if [file exists work] {vdel -all}
vlib work
vcom threebitcounter.vhd
vlog tb_top.v -sv
vsim tb_top;
run -all
