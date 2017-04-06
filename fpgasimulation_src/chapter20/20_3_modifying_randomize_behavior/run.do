if [file exists work] {vdel -all}
vlib work
vlog top.sv
vsim -c top -sv_seed 5
run -all
quit -f
