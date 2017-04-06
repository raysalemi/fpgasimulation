if [file exists work] {vdel -all}
vlib work
vlog top.v threebitcounter.v -y . +libext+.v  -sv +define+ASSERTIONS_OFF
vsim top;
run -all
