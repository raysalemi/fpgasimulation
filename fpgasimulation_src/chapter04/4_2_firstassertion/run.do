if [file exists work] {vdel -all}
vlib work
vlog firstassert.v top.v
vsim top;
run -all
