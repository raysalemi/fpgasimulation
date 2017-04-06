if [file exists work] {vdel -all}
vlib work
vlog top.v
vsim -c top
run
quit -f
