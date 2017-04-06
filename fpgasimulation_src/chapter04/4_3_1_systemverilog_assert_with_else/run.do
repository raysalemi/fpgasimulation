if [file exists work] {vdel -all}
vlib work
vlog tb_top.v threebitcounter.v -sv

vsim tb_top;
set ignoreSVAWarning 0
run -all
