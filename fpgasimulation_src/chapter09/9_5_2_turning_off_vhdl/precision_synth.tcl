//  Precision Synthesis 2006a.112 (Production Release) Thu Dec 21 00:28:44 PST 2006
//  
//  Copyright (c) Mentor Graphics Corporation, 1996-2006, All Rights Reserved.
//             Portions copyright 1991-2004 Compuware Corporation
//                       UNPUBLISHED, LICENSED SOFTWARE.
//            CONFIDENTIAL AND PROPRIETARY INFORMATION WHICH IS THE
//          PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS
//  
//  Running on Windows XP rsalemi@MAW-RSALEMI-LT Service Pack 2 5.01.2600 i686
//  
//  Start time Thu Aug 23 12:14:44 2007

add_input_file {
../../std_ovl/std_ovl.vhd 
../../std_ovl/std_ovl_components.vhd 
../../std_ovl/vhdl93/syn_src/std_ovl_procs_syn.vhd 
../../std_ovl/std_ovl_clock_gating.vhd 
../../std_ovl/std_ovl_reset_gating.vhd

../../std_ovl/ovl_always.vhd
../../std_ovl/ovl_cycle_sequence.vhd
../../std_ovl/ovl_implication.vhd
../../std_ovl/ovl_never.vhd
../../std_ovl/ovl_never_unknown_async.vhd
../../std_ovl/ovl_never_unknown.vhd
../../std_ovl/ovl_next.vhd
../../std_ovl/ovl_one_hot.vhd
../../std_ovl/ovl_range.vhd
../../std_ovl/ovl_zero_one_hot.vhd

../../std_ovl/vhdl93/syn_src/ovl_always_rtl.vhd
../../std_ovl/vhdl93/syn_src/ovl_cycle_sequence_rtl.vhd
../../std_ovl/vhdl93/syn_src/ovl_implication_rtl.vhd
ovl_never_rtl.vhd
../../std_ovl/vhdl93/syn_src/ovl_never_unknown_async_rtl.vhd
../../std_ovl/vhdl93/syn_src/ovl_never_unknown_rtl.vhd
../../std_ovl/vhdl93/syn_src/ovl_next_rtl.vhd
../../std_ovl/vhdl93/syn_src/ovl_one_hot_rtl.vhd
../../std_ovl/vhdl93/syn_src/ovl_range_rtl.vhd
../../std_ovl/vhdl93/syn_src/ovl_zero_one_hot_rtl.vhd
} -work accellera_ovl_vhdl

add_input_file {
control_record.vhd
threebitcounter_assert.vhd
threebitcounter.vhd}


setup_design -manufacturer Xilinx -family SPARTAN3 -part 3s50tq144 -speed 4
compile
