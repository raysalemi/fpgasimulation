if {[file exists accellera_ovl_vhdl]==0} {
  vlib accellera_ovl_vhdl
  vcom -work accellera_ovl_vhdl -f compile_ovl.f   
  vlib accellera_ovl_vhdl_u
  vcom -work accellera_ovl_vhdl_u ../../std_ovl/std_ovl_u_components.vhd
}

if [file exists work] {vdel -lib work -all}
vlib work
vcom -f compile_vhdl.f
vsim -novopt tb_top;
log -r /*
set NoQuitOnFinish 1
set NumericStdNoWarnings 1
set StdArithNoWarnings 1
run 200ns
quit -f
