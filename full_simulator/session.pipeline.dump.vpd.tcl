# Begin_DVE_Session_Save_Info
# DVE view(Wave.1 ) session
# Saved on Tue May 8 16:36:39 2018
# Toplevel windows open: 2
# 	TopLevel.1
# 	TopLevel.2
#   Wave.1: 33 signals
# End_DVE_Session_Save_Info

# DVE version: K-2015.09-SP1_Full64
# DVE build date: Nov 24 2015 21:15:24


#<Session mode="View" path="/home/ecelrc/students/sflolid/micro/finalproj/fresh/lc86/full_simulator/session.pipeline.dump.vpd.tcl" type="Debug">

#<Database>

gui_set_time_units 1ps
#</Database>

# DVE View/pane content session: 

# Begin_DVE_Session_Save_Info (Wave.1)
# DVE wave signals session
# Saved on Tue May 8 16:36:39 2018
# 33 signals
# End_DVE_Session_Save_Info

# DVE version: K-2015.09-SP1_Full64
# DVE build date: Nov 24 2015 21:15:24


#Add ncecessay scopes
gui_load_child_values {TOP.u_full_simulator.u_pipeline.u_icache}
gui_load_child_values {TOP.u_full_simulator.u_full_memory}
gui_load_child_values {TOP.u_full_simulator.u_full_memory.ICACHE_PORT}
gui_load_child_values {TOP.u_full_simulator}
gui_load_child_values {TOP.u_full_simulator.u_pipeline}
gui_load_child_values {TOP}

gui_set_time_units 1ps

set _wave_session_group_6 Clocks
if {[gui_sg_is_group -name "$_wave_session_group_6"]} {
    set _wave_session_group_6 [gui_sg_generate_new_name]
}
set Group1 "$_wave_session_group_6"

gui_sg_addsignal -group "$_wave_session_group_6" { {V1:TOP.clk} {V1:TOP.bus_clk} }

set _wave_session_group_7 {$ to BUS INTERFACE}
if {[gui_sg_is_group -name "$_wave_session_group_7"]} {
    set _wave_session_group_7 [gui_sg_generate_new_name]
}
set Group2 "$_wave_session_group_7"

gui_sg_addsignal -group "$_wave_session_group_7" { }

set _wave_session_group_8 $_wave_session_group_7|
append _wave_session_group_8 ICACHE
set {$ to BUS INTERFACE|ICACHE} "$_wave_session_group_8"

gui_sg_addsignal -group "$_wave_session_group_8" { {V1:TOP.u_full_simulator.IC_EN} {V1:TOP.u_full_simulator.IC_WRITE_DATA} {V1:TOP.u_full_simulator.IC_READ_DATA} {V1:TOP.u_full_simulator.u_full_memory.IC_R} {V1:TOP.u_full_simulator.IC_R} {V1:TOP.u_full_simulator.u_pipeline.ICACHE_BUS_READY} }

set _wave_session_group_9 $_wave_session_group_7|
append _wave_session_group_9 DCACHE
set {$ to BUS INTERFACE|DCACHE} "$_wave_session_group_9"

gui_sg_addsignal -group "$_wave_session_group_9" { {V1:TOP.u_full_simulator.DC_EN} {V1:TOP.u_full_simulator.DC_WRITE_DATA} {V1:TOP.u_full_simulator.DC_READ_DATA} }

gui_sg_move "$_wave_session_group_9" -after "$_wave_session_group_7" -pos 1 

set _wave_session_group_10 {FULL MEMORY}
if {[gui_sg_is_group -name "$_wave_session_group_10"]} {
    set _wave_session_group_10 [gui_sg_generate_new_name]
}
set Group3 "$_wave_session_group_10"

gui_sg_addsignal -group "$_wave_session_group_10" { {V1:TOP.u_full_simulator.u_full_memory.D} {V1:TOP.u_full_simulator.u_full_memory.A} {V1:TOP.u_full_simulator.u_full_memory.SIZE} {V1:TOP.u_full_simulator.u_full_memory.RW} }

set _wave_session_group_11 $_wave_session_group_10|
append _wave_session_group_11 {IC PORT}
set {FULL MEMORY|IC PORT} "$_wave_session_group_11"

gui_sg_addsignal -group "$_wave_session_group_11" { {V1:TOP.u_full_simulator.u_full_memory.ICACHE_PORT.current_state} }

gui_sg_move "$_wave_session_group_11" -after "$_wave_session_group_10" -pos 4 

set _wave_session_group_12 PIPELINE
if {[gui_sg_is_group -name "$_wave_session_group_12"]} {
    set _wave_session_group_12 [gui_sg_generate_new_name]
}
set Group4 "$_wave_session_group_12"

gui_sg_addsignal -group "$_wave_session_group_12" { } 

set _wave_session_group_13 ICACHE
if {[gui_sg_is_group -name "$_wave_session_group_13"]} {
    set _wave_session_group_13 [gui_sg_generate_new_name]
}
set Group5 "$_wave_session_group_13"

gui_sg_addsignal -group "$_wave_session_group_13" { {V1:TOP.u_full_simulator.u_pipeline.u_icache.CLK} {V1:TOP.u_full_simulator.u_pipeline.u_icache.current_state} {V1:TOP.u_full_simulator.u_pipeline.u_icache.SET} {V1:TOP.u_full_simulator.u_pipeline.u_icache.RST} {V1:TOP.u_full_simulator.u_pipeline.u_icache.data_write} {V1:TOP.u_full_simulator.u_pipeline.u_icache.RW} {V1:TOP.u_full_simulator.u_pipeline.u_icache.enable} {V1:TOP.u_full_simulator.u_pipeline.u_icache.addr} {V1:TOP.u_full_simulator.u_pipeline.u_icache.size} {V1:TOP.u_full_simulator.u_pipeline.u_icache.data_read_out} {V1:TOP.u_full_simulator.u_pipeline.u_icache.ready} {V1:TOP.u_full_simulator.u_pipeline.u_icache.BUS_WR} {V1:TOP.u_full_simulator.u_pipeline.u_icache.BUS_EN} {V1:TOP.u_full_simulator.u_pipeline.u_icache.BUS_ADDR} {V1:TOP.u_full_simulator.u_pipeline.u_icache.BUS_WRITE} {V1:TOP.u_full_simulator.u_pipeline.u_icache.BUS_R} {V1:TOP.u_full_simulator.u_pipeline.u_icache.BUS_READ} }
if {![info exists useOldWindow]} { 
	set useOldWindow true
}
if {$useOldWindow && [string first "Wave" [gui_get_current_window -view]]==0} { 
	set Wave.1 [gui_get_current_window -view] 
} else {
	set Wave.1 [lindex [gui_get_window_ids -type Wave] 0]
if {[string first "Wave" ${Wave.1}]!=0} {
gui_open_window Wave
set Wave.1 [ gui_get_current_window -view ]
}
}

set groupExD [gui_get_pref_value -category Wave -key exclusiveSG]
gui_set_pref_value -category Wave -key exclusiveSG -value {false}
set origWaveHeight [gui_get_pref_value -category Wave -key waveRowHeight]
gui_list_set_height -id Wave -height 25
set origGroupCreationState [gui_list_create_group_when_add -wave]
gui_list_create_group_when_add -wave -disable
gui_marker_set_ref -id ${Wave.1}  C1
gui_wv_zoom_timerange -id ${Wave.1} 1786605 2177231
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group1}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group2}]
gui_list_add_group -id ${Wave.1}  -after ${Group2} [list ${$ to BUS INTERFACE|ICACHE}]
gui_list_add_group -id ${Wave.1} -after {$ to BUS INTERFACE|ICACHE} [list ${$ to BUS INTERFACE|DCACHE}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group3}]
gui_list_add_group -id ${Wave.1}  -after TOP.u_full_simulator.u_full_memory.RW [list ${FULL MEMORY|IC PORT}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group4}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group5}]
gui_list_collapse -id ${Wave.1} ${Group2}
gui_list_collapse -id ${Wave.1} ${$ to BUS INTERFACE|ICACHE}
gui_list_collapse -id ${Wave.1} ${$ to BUS INTERFACE|DCACHE}
gui_list_collapse -id ${Wave.1} ${Group3}
gui_list_collapse -id ${Wave.1} ${Group5}
gui_seek_criteria -id ${Wave.1} {Any Edge}

gui_list_alias -id ${Wave.1} -group ${Group5} -index 0 -signal V1:TOP.u_full_simulator.u_pipeline.u_icache.current_state -add IC_STATE 

gui_set_pref_value -category Wave -key exclusiveSG -value $groupExD
gui_list_set_height -id Wave -height $origWaveHeight
if {$origGroupCreationState} {
	gui_list_create_group_when_add -wave -enable
}
if { $groupExD } {
 gui_msg_report -code DVWW028
}
gui_list_set_filter -id ${Wave.1} -list { {Buffer 1} {Input 1} {Others 1} {Linkage 1} {Output 1} {Parameter 1} {All 1} {Aggregate 1} {LibBaseMember 1} {Event 1} {Assertion 1} {Constant 1} {Interface 1} {BaseMembers 1} {Signal 1} {$unit 1} {Inout 1} {Variable 1} }
gui_list_set_filter -id ${Wave.1} -text {*}
gui_list_set_insertion_bar  -id ${Wave.1} -group ${Group3}  -position in

gui_marker_move -id ${Wave.1} {C1} 1814970
gui_view_scroll -id ${Wave.1} -vertical -set 0
gui_show_grid -id ${Wave.1} -enable false
#</Session>
