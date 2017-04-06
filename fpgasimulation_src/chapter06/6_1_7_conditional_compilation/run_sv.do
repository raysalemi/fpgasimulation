if [file exists work] {vdel -all}
vlib work
vlog top.v threebitcounter.v -y . +libext+.v  -sv
vsim top;
run -all
