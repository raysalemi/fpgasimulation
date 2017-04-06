if [file exists "work"] {vdel -all}
vlib work
vlog -f compile_sv.f 
vcom -f compile_vhdl.f
set contents [glob -directory tests *]
foreach item $contents {
	file copy -force $item ./test_constraint.svh
	vlog alu_tester.sv
	puts "*******************************************"
	puts "*******************************************"
	puts "                 $item"
	puts "*******************************************"
	puts "*******************************************"
	set testpath [split $item "/"]
	set testfile [split [lindex $testpath 1] "."]
	set testname [lindex $testfile 0]
	vsim top -novopt -coverage -debugDB=debug/$testname.dbg -wlf debug/$testname.wlf -l debug/$testname.txt -assertdebug
	set NoQuitOnFinish 1
	onbreak {resume}
	log -r /*
	run -all	
}

quit -f



