if [file exists work] {vdel -all}
vlib work
vlog -f compile.f 
vcom threebitcounter.vhd
vsim top;
run -all
