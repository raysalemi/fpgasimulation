if [file exists "work"] {vdel -all}
vlib work
vlog -f compile.f
vsim top
run 50
quit -f

