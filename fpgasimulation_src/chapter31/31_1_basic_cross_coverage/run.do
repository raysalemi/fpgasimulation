if [file exists work] {vdel -all}
vlib work
vlog top.sv
vsim top -coverage
run -all
coverage report -cvg -details
quit -f
