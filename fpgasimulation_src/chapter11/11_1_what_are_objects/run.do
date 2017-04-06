if [file exists work] {vdel -all}
vlib work
vlog circle.sv
vsim -c circle_mod
run 1
quit
