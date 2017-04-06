if [file exists work] {vdel -all}
vlib work
vlog tb_top.v threebitcounter.v -vlog95compat
vsim tb_top;
run -all
