if [file exists work] {vdel -all}
vlib work
vlog top.v +define+DOCTOR
quit -f


