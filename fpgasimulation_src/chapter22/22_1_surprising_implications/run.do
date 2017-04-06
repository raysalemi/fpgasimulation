if [file exists work] {vdel -all}
if [file exists tran_out.txt] {exec rm tran_out.txt}
if [file exists rtl_out.txt ] {exec rm rtl_out.txt}
vlib work
vlog top.sv
vsim top -sv_seed 13
run -all
quit -f






