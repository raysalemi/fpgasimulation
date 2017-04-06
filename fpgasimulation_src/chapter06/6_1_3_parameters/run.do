if [file exists work] {vdel -all}
vlib work
vlog top.v
vsim top;
run -all
quit -f
