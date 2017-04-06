if [file exists work] {vdel -all}
vlib work
vlog top.sv
vsim top 
run -all
quit -f
