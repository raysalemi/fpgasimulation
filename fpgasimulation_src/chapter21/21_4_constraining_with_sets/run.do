if [file exists work] {vdel -all}
vlib work
vlog top.sv
vsim -novopt top -sv_seed 1
run -all
quit







