# Begin_DVE_Session_Save_Info
# DVE view(Wave.1 ) session
# Saved on Mon May 7 12:08:55 2018
# Toplevel windows open: 2
# 	TopLevel.1
# 	TopLevel.2
#   Wave.1: 24 signals
# End_DVE_Session_Save_Info

# DVE version: K-2015.09-SP1_Full64
# DVE build date: Nov 24 2015 21:15:24


#<Session mode="View" path="/home/ecelrc/students/sflolid/micro/finalproj/fresh/lc86/memory/session.all_mem.dump.vpd.tcl" type="Debug">

#<Database>

gui_set_time_units 1ps
#</Database>

# DVE View/pane content session: 

# Begin_DVE_Session_Save_Info (Wave.1)
# DVE wave signals session
# Saved on Mon May 7 12:08:55 2018
# 24 signals
# End_DVE_Session_Save_Info

# DVE version: K-2015.09-SP1_Full64
# DVE build date: Nov 24 2015 21:15:24


#Add ncecessay scopes
gui_load_child_values {TOP.full_memory_u.arbitrator_u}
gui_load_child_values {TOP.full_memory_u.main_memory_u}
gui_load_child_values {TOP.full_memory_u}
gui_load_child_values {TOP.full_memory_u.mem_bus_controller_u}
gui_load_child_values {TOP}
gui_load_child_values {TOP.full_memory_u.DCACHE_PORT}

gui_set_time_units 1ps

set _wave_session_group_1 {Bus Signals}
if {[gui_sg_is_group -name "$_wave_session_group_1"]} {
    set _wave_session_group_1 [gui_sg_generate_new_name]
}
set Group1 "$_wave_session_group_1"

gui_sg_addsignal -group "$_wave_session_group_1" { {V1:TOP.full_memory_u.D} {V1:TOP.full_memory_u.A} {V1:TOP.full_memory_u.SIZE} {V1:TOP.full_memory_u.RW} {V1:TOP.full_memory_u.ACK_OUT} {V1:TOP.full_memory_u.ACK_IN} }

set _wave_session_group_2 Clock
if {[gui_sg_is_group -name "$_wave_session_group_2"]} {
    set _wave_session_group_2 [gui_sg_generate_new_name]
}
set Group2 "$_wave_session_group_2"

gui_sg_addsignal -group "$_wave_session_group_2" { {V1:TOP.clk} }

set _wave_session_group_3 {DC port}
if {[gui_sg_is_group -name "$_wave_session_group_3"]} {
    set _wave_session_group_3 [gui_sg_generate_new_name]
}
set Group3 "$_wave_session_group_3"

gui_sg_addsignal -group "$_wave_session_group_3" { {V1:TOP.full_memory_u.DCACHE_PORT.current_state} {V1:TOP.full_memory_u.DCACHE_PORT.current_size} {V1:TOP.full_memory_u.DCACHE_PORT.data_buffer_out} }

set _wave_session_group_4 Arbitrator
if {[gui_sg_is_group -name "$_wave_session_group_4"]} {
    set _wave_session_group_4 [gui_sg_generate_new_name]
}
set Group4 "$_wave_session_group_4"

gui_sg_addsignal -group "$_wave_session_group_4" { {V1:TOP.full_memory_u.arbitrator_u.current_state} {V1:TOP.full_memory_u.BR} {V1:TOP.full_memory_u.BG} {V1:TOP.full_memory_u.arbitrator_u.REQ} {V1:TOP.full_memory_u.arbitrator_u.DONE} }

set _wave_session_group_5 {MEM port}
if {[gui_sg_is_group -name "$_wave_session_group_5"]} {
    set _wave_session_group_5 [gui_sg_generate_new_name]
}
set Group5 "$_wave_session_group_5"

gui_sg_addsignal -group "$_wave_session_group_5" { {V1:TOP.full_memory_u.mem_bus_controller_u.MEM_INOUT} {V1:TOP.full_memory_u.mem_bus_controller_u.current_state} {V1:TOP.full_memory_u.mem_bus_controller_u.data_buffer_out} {V1:TOP.full_memory_u.mem_bus_controller_u.rd_data_buffer_out} }

set _wave_session_group_6 {Main Memory}
if {[gui_sg_is_group -name "$_wave_session_group_6"]} {
    set _wave_session_group_6 [gui_sg_generate_new_name]
}
set Group6 "$_wave_session_group_6"

gui_sg_addsignal -group "$_wave_session_group_6" { {V1:TOP.full_memory_u.main_memory_u.ADDR} {V1:TOP.full_memory_u.main_memory_u.WR} {V1:TOP.full_memory_u.main_memory_u.EN} {V1:TOP.full_memory_u.main_memory_u.WRITE_SIZE} {V1:TOP.full_memory_u.main_memory_u.DATA_BUF} }
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
gui_wv_zoom_timerange -id ${Wave.1} 0 960000
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group1}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group2}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group3}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group4}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group5}]
gui_list_add_group -id ${Wave.1} -after {New Group} [list ${Group6}]
gui_list_collapse -id ${Wave.1} ${Group1}
gui_list_collapse -id ${Wave.1} ${Group3}
gui_list_collapse -id ${Wave.1} ${Group4}
gui_list_collapse -id ${Wave.1} ${Group5}
gui_list_collapse -id ${Wave.1} ${Group6}
gui_seek_criteria -id ${Wave.1} {Any Edge}

gui_list_alias -id ${Wave.1} -group ${Group3} -index 0 -signal V1:TOP.full_memory_u.DCACHE_PORT.current_state -add State 
gui_list_alias -id ${Wave.1} -group ${Group3} -index 0 -signal V1:TOP.full_memory_u.DCACHE_PORT.current_size -add Size 
gui_list_alias -id ${Wave.1} -group ${Group3} -index 0 -signal V1:TOP.full_memory_u.DCACHE_PORT.data_buffer_out -add DATA_BUF 
gui_list_alias -id ${Wave.1} -group ${Group4} -index 0 -signal V1:TOP.full_memory_u.arbitrator_u.current_state -add ARB_STATE 
gui_list_alias -id ${Wave.1} -group ${Group5} -index 0 -signal V1:TOP.full_memory_u.mem_bus_controller_u.current_state -add MEM_State 

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
gui_list_set_insertion_bar  -id ${Wave.1} -group ${Group5}  -position in

gui_marker_move -id ${Wave.1} {C1} 48320
gui_view_scroll -id ${Wave.1} -vertical -set 0
gui_show_grid -id ${Wave.1} -enable false
#</Session>

