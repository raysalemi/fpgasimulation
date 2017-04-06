if [file exists work] {vdel -all}
vlib work
vlog +libext+.v -y raylib top.v
quit -f


