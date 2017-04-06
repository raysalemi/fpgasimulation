onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -format Logic /top/pmon/check_ack/clk
add wave -noupdate -format Logic /top/pmon/check_ack/reset_n
add wave -noupdate -format Logic /top/pmon/check_ack/req
add wave -noupdate -format Logic /top/pmon/check_ack/ack
add wave -noupdate -format Literal /top/pmon/check_ack/ovl_assert/a_assert_handshake_ack_min_cycle/A_ASSERT_HANDSHAKE_ACK_MIN_CYCLE_P/A_ASSERT_HANDSHAKE_ACK_MIN_CYCLE_P_THREAD_MONITOR.0
TreeUpdate [SetDefaultTree]
configure wave -namecolwidth 142
configure wave -valuecolwidth 96
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ns} {150 ns}
