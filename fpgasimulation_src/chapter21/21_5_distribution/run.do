if [file exists work] {vdel -all}
vlib work
vlog top.sv
vsim top -sv_seed 30
run -all
quit






