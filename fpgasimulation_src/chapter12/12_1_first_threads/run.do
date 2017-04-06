if [file exists "work"] {vdel -all}
vlib work
vlog first_threads.sv
vsim first_threads
run 1
quit
