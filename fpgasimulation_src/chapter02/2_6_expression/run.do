if [file exists work] {vdel -all}
vlib work
vlog -f compile.f
vlog -coverExcludeDefault -cover e tiny_cache.v
vsim -coverage top -novopt
set NoQuitOnFinish 1
set NumericStdNoWarnings 1
set StdArithNoWarnings 1
onbreak {resume};
run -all
coverage report -details -file coverage.txt


