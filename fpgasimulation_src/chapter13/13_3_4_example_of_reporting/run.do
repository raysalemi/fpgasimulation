if [file exists work] {vdel -all}
vlib work
vlog +incdir+../../ovm/src ../../ovm/src/ovm_pkg.sv
vlog top.sv
vsim -c top
run 1
quit
