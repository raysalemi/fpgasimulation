if [file exists work] {vdel -all}
vlib work
vlog top.sv
vsim -c top
run 1
quit
