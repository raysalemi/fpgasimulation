if [file exists "work"] {vdel -all}
vlib work
vlog +incdir+../../ovm/src ../../ovm/src/ovm_pkg.sv
vlog good_threads.sv
vsim good_threads
run 1
quit
