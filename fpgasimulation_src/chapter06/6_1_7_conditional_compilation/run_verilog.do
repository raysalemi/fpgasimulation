if [file exists work] {vdel -all}
vlib work
vlog top.v threebitcounter.v -y . +libext+.v -vlog95compat +define+VERILOG
vsim top;
run -all
