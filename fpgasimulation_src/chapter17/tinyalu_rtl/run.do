if [file exists "work"] {vdel -all}
vlib work
vlog -f compile_sv.f 
vcom -f compile_vhdl.f
vsim top -novopt -assertdebug
onbreak {resume}
log -r /*
run -all
quit -f




