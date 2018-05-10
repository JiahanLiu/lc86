# Begin_DVE_Session_Save_Info
# DVE full session
# Saved on Thu May 10 00:49:06 2018
# Designs open: 1
#   V1: pipeline.dump.vpd
# Toplevel windows open: 2
# 	TopLevel.1
# 	TopLevel.2
#   Source.1: TOP.u_full_simulator.u_pipeline.u_lsu_controller
#   Wave.1: 82 signals
#   Group count = 6
#   Group Group1 signal count = 16
#   Group u_repne_support signal count = 13
#   Group Group2 signal count = 16
#   Group Group3 signal count = 21
# End_DVE_Session_Save_Info

# DVE version: K-2015.09-SP1_Full64
# DVE build date: Nov 24 2015 21:15:24


#<Session mode="Full" path="/home/ecelrc/students/anarkhede/micro/lc86/full_simulator/session.pipeline_cmps.dump.vpd.tcl" type="Debug">

gui_set_loading_session_type Post
gui_continuetime_set

# Close design
if { [gui_sim_state -check active] } {
    gui_sim_terminate
}
gui_close_db -all
gui_expr_clear_all

# Close all windows
gui_close_window -type Console
gui_close_window -type Wave
gui_close_window -type Source
gui_close_window -type Schematic
gui_close_window -type Data
gui_close_window -type DriverLoad
gui_close_window -type List
gui_close_window -type Memory
gui_close_window -type HSPane
gui_close_window -type DLPane
gui_close_window -type Assertion
gui_close_window -type CovHier
gui_close_window -type CoverageTable
gui_close_window -type CoverageMap
gui_close_window -type CovDetail
gui_close_window -type Local
gui_close_window -type Stack
gui_close_window -type Watch
gui_close_window -type Group
gui_close_window -type Transaction



# Application preferences
gui_set_pref_value -key app_default_font -value {Helvetica,10,-1,5,50,0,0,0,0,0}
gui_src_preferences -tabstop 8 -maxbits 24 -windownumber 1
#<WindowLayout>

# DVE top-level session


# Create and position top-level window: TopLevel.1

if {![gui_exist_window -window TopLevel.1]} {
    set TopLevel.1 [ gui_create_window -type TopLevel \
       -icon $::env(DVE)/auxx/gui/images/toolbars/dvewin.xpm] 
} else { 
    set TopLevel.1 TopLevel.1
}
gui_show_window -window ${TopLevel.1} -show_state maximized -rect {{73 27} {1919 934}}

# ToolBar settings
gui_set_toolbar_attributes -toolbar {TimeOperations} -dock_state top
gui_set_toolbar_attributes -toolbar {TimeOperations} -offset 0
gui_show_toolbar -toolbar {TimeOperations}
gui_hide_toolbar -toolbar {&File}
gui_set_toolbar_attributes -toolbar {&Edit} -dock_state top
gui_set_toolbar_attributes -toolbar {&Edit} -offset 0
gui_show_toolbar -toolbar {&Edit}
gui_hide_toolbar -toolbar {CopyPaste}
gui_set_toolbar_attributes -toolbar {&Trace} -dock_state top
gui_set_toolbar_attributes -toolbar {&Trace} -offset 0
gui_show_toolbar -toolbar {&Trace}
gui_hide_toolbar -toolbar {TraceInstance}
gui_hide_toolbar -toolbar {BackTrace}
gui_set_toolbar_attributes -toolbar {&Scope} -dock_state top
gui_set_toolbar_attributes -toolbar {&Scope} -offset 0
gui_show_toolbar -toolbar {&Scope}
gui_set_toolbar_attributes -toolbar {&Window} -dock_state top
gui_set_toolbar_attributes -toolbar {&Window} -offset 0
gui_show_toolbar -toolbar {&Window}
gui_set_toolbar_attributes -toolbar {Signal} -dock_state top
gui_set_toolbar_attributes -toolbar {Signal} -offset 0
gui_show_toolbar -toolbar {Signal}
gui_set_toolbar_attributes -toolbar {Zoom} -dock_state top
gui_set_toolbar_attributes -toolbar {Zoom} -offset 0
gui_show_toolbar -toolbar {Zoom}
gui_set_toolbar_attributes -toolbar {Zoom And Pan History} -dock_state top
gui_set_toolbar_attributes -toolbar {Zoom And Pan History} -offset 0
gui_show_toolbar -toolbar {Zoom And Pan History}
gui_set_toolbar_attributes -toolbar {Grid} -dock_state top
gui_set_toolbar_attributes -toolbar {Grid} -offset 0
gui_show_toolbar -toolbar {Grid}
gui_hide_toolbar -toolbar {Simulator}
gui_hide_toolbar -toolbar {Interactive Rewind}
gui_hide_toolbar -toolbar {Testbench}

# End ToolBar settings

# Docked window settings
set HSPane.1 [gui_create_window -type HSPane -parent ${TopLevel.1} -dock_state left -dock_on_new_line true -dock_extent 176]
catch { set Hier.1 [gui_share_window -id ${HSPane.1} -type Hier] }
gui_set_window_pref_key -window ${HSPane.1} -key dock_width -value_type integer -value 176
gui_set_window_pref_key -window ${HSPane.1} -key dock_height -value_type integer -value -1
gui_set_window_pref_key -window ${HSPane.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${HSPane.1} {{left 0} {top 0} {width 175} {height 647} {dock_state left} {dock_on_new_line true} {child_hier_colhier 140} {child_hier_coltype 100} {child_hier_colpd 0} {child_hier_col1 0} {child_hier_col2 1} {child_hier_col3 -1}}
set DLPane.1 [gui_create_window -type DLPane -parent ${TopLevel.1} -dock_state left -dock_on_new_line true -dock_extent 317]
catch { set Data.1 [gui_share_window -id ${DLPane.1} -type Data] }
gui_set_window_pref_key -window ${DLPane.1} -key dock_width -value_type integer -value 317
gui_set_window_pref_key -window ${DLPane.1} -key dock_height -value_type integer -value 826
gui_set_window_pref_key -window ${DLPane.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${DLPane.1} {{left 0} {top 0} {width 316} {height 647} {dock_state left} {dock_on_new_line true} {child_data_colvariable 182} {child_data_colvalue 100} {child_data_coltype 56} {child_data_col1 0} {child_data_col2 1} {child_data_col3 2}}
set Console.1 [gui_create_window -type Console -parent ${TopLevel.1} -dock_state bottom -dock_on_new_line true -dock_extent 141]
gui_set_window_pref_key -window ${Console.1} -key dock_width -value_type integer -value -1
gui_set_window_pref_key -window ${Console.1} -key dock_height -value_type integer -value 141
gui_set_window_pref_key -window ${Console.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${Console.1} {{left 0} {top 0} {width 295} {height 179} {dock_state bottom} {dock_on_new_line true}}
set DriverLoad.1 [gui_create_window -type DriverLoad -parent ${TopLevel.1} -dock_state bottom -dock_on_new_line false -dock_extent 180]
gui_set_window_pref_key -window ${DriverLoad.1} -key dock_width -value_type integer -value 150
gui_set_window_pref_key -window ${DriverLoad.1} -key dock_height -value_type integer -value 180
gui_set_window_pref_key -window ${DriverLoad.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${DriverLoad.1} {{left 0} {top 0} {width 1550} {height 179} {dock_state bottom} {dock_on_new_line false}}
#### Start - Readjusting docked view's offset / size
set dockAreaList { top left right bottom }
foreach dockArea $dockAreaList {
  set viewList [gui_ekki_get_window_ids -active_parent -dock_area $dockArea]
  foreach view $viewList {
      if {[lsearch -exact [gui_get_window_pref_keys -window $view] dock_width] != -1} {
        set dockWidth [gui_get_window_pref_value -window $view -key dock_width]
        set dockHeight [gui_get_window_pref_value -window $view -key dock_height]
        set offset [gui_get_window_pref_value -window $view -key dock_offset]
        if { [string equal "top" $dockArea] || [string equal "bottom" $dockArea]} {
          gui_set_window_attributes -window $view -dock_offset $offset -width $dockWidth
        } else {
          gui_set_window_attributes -window $view -dock_offset $offset -height $dockHeight
        }
      }
  }
}
#### End - Readjusting docked view's offset / size
gui_sync_global -id ${TopLevel.1} -option true

# MDI window settings
set Source.1 [gui_create_window -type {Source}  -parent ${TopLevel.1}]
gui_show_window -window ${Source.1} -show_state maximized
gui_update_layout -id ${Source.1} {{show_state maximized} {dock_state undocked} {dock_on_new_line false}}

# End MDI window settings


# Create and position top-level window: TopLevel.2

if {![gui_exist_window -window TopLevel.2]} {
    set TopLevel.2 [ gui_create_window -type TopLevel \
       -icon $::env(DVE)/auxx/gui/images/toolbars/dvewin.xpm] 
} else { 
    set TopLevel.2 TopLevel.2
}
gui_show_window -window ${TopLevel.2} -show_state normal -rect {{73 59} {1915 910}}

# ToolBar settings
gui_set_toolbar_attributes -toolbar {TimeOperations} -dock_state top
gui_set_toolbar_attributes -toolbar {TimeOperations} -offset 0
gui_show_toolbar -toolbar {TimeOperations}
gui_hide_toolbar -toolbar {&File}
gui_set_toolbar_attributes -toolbar {&Edit} -dock_state top
gui_set_toolbar_attributes -toolbar {&Edit} -offset 0
gui_show_toolbar -toolbar {&Edit}
gui_hide_toolbar -toolbar {CopyPaste}
gui_set_toolbar_attributes -toolbar {&Trace} -dock_state top
gui_set_toolbar_attributes -toolbar {&Trace} -offset 0
gui_show_toolbar -toolbar {&Trace}
gui_hide_toolbar -toolbar {TraceInstance}
gui_hide_toolbar -toolbar {BackTrace}
gui_set_toolbar_attributes -toolbar {&Scope} -dock_state top
gui_set_toolbar_attributes -toolbar {&Scope} -offset 0
gui_show_toolbar -toolbar {&Scope}
gui_set_toolbar_attributes -toolbar {&Window} -dock_state top
gui_set_toolbar_attributes -toolbar {&Window} -offset 0
gui_show_toolbar -toolbar {&Window}
gui_set_toolbar_attributes -toolbar {Signal} -dock_state top
gui_set_toolbar_attributes -toolbar {Signal} -offset 0
gui_show_toolbar -toolbar {Signal}
gui_set_toolbar_attributes -toolbar {Zoom} -dock_state top
gui_set_toolbar_attributes -toolbar {Zoom} -offset 0
gui_show_toolbar -toolbar {Zoom}
gui_set_toolbar_attributes -toolbar {Zoom And Pan History} -dock_state top
gui_set_toolbar_attributes -toolbar {Zoom And Pan History} -offset 0
gui_show_toolbar -toolbar {Zoom And Pan History}
gui_set_toolbar_attributes -toolbar {Grid} -dock_state top
gui_set_toolbar_attributes -toolbar {Grid} -offset 0
gui_show_toolbar -toolbar {Grid}
gui_hide_toolbar -toolbar {Simulator}
gui_hide_toolbar -toolbar {Interactive Rewind}
gui_set_toolbar_attributes -toolbar {Testbench} -dock_state top
gui_set_toolbar_attributes -toolbar {Testbench} -offset 0
gui_show_toolbar -toolbar {Testbench}

# End ToolBar settings

# Docked window settings
gui_sync_global -id ${TopLevel.2} -option true

# MDI window settings
set Wave.1 [gui_create_window -type {Wave}  -parent ${TopLevel.2}]
gui_show_window -window ${Wave.1} -show_state maximized
gui_update_layout -id ${Wave.1} {{show_state maximized} {dock_state undocked} {dock_on_new_line false} {child_wave_left 534} {child_wave_right 1303} {child_wave_colname 265} {child_wave_colvalue 265} {child_wave_col1 0} {child_wave_col2 1}}

# End MDI window settings

gui_set_env TOPLEVELS::TARGET_FRAME(Source) ${TopLevel.1}
gui_set_env TOPLEVELS::TARGET_FRAME(Schematic) ${TopLevel.1}
gui_set_env TOPLEVELS::TARGET_FRAME(PathSchematic) ${TopLevel.1}
gui_set_env TOPLEVELS::TARGET_FRAME(Wave) none
gui_set_env TOPLEVELS::TARGET_FRAME(List) none
gui_set_env TOPLEVELS::TARGET_FRAME(Memory) ${TopLevel.1}
gui_set_env TOPLEVELS::TARGET_FRAME(DriverLoad) none
gui_update_statusbar_target_frame ${TopLevel.1}
gui_update_statusbar_target_frame ${TopLevel.2}

#</WindowLayout>

#<Database>

# DVE Open design session: 

if { ![gui_is_db_opened -db {pipeline.dump.vpd}] } {
	gui_open_db -design V1 -file pipeline.dump.vpd -nosource
}
gui_set_precision 1ps
gui_set_time_units 1ns
#</Database>

# DVE Global setting session: 


# Global: Bus

# Global: Expressions

# Global: Signal Time Shift

# Global: Signal Compare

# Global: Signal Groups
gui_load_child_values {TOP.u_full_simulator.u_pipeline.u_execute.u_operand_select_ex}
gui_load_child_values {TOP.u_full_simulator.u_pipeline.u_execute}
gui_load_child_values {TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb}
gui_load_child_values {TOP.u_full_simulator.u_pipeline.u_execute.u_repne_support}
gui_load_child_values {TOP.u_full_simulator.u_pipeline.or_ld_ex}


set _session_group_30 Group1
gui_sg_create "$_session_group_30"
set Group1 "$_session_group_30"

gui_sg_addsignal -group "$_session_group_30" { TOP.u_full_simulator.u_pipeline.AG_control_address_debug TOP.u_full_simulator.u_pipeline.AG2_control_address_debug TOP.u_full_simulator.u_pipeline.ME_control_address_debug_out TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_DR1 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_DR2 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_DR3 TOP.u_full_simulator.u_pipeline.WB_control_address_debug TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_data1 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_data2 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_data3 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_gpr1 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_gpr2 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_gpr3 TOP.u_full_simulator.u_pipeline.ME2_control_address_debug_out TOP.u_full_simulator.u_pipeline.u_memory_stage2.MEM_RD_ADDR TOP.u_full_simulator.u_pipeline.u_memory_stage2.MEM_WR_ADDR }

set _session_group_31 u_repne_support
gui_sg_create "$_session_group_31"
set u_repne_support "$_session_group_31"

gui_sg_addsignal -group "$_session_group_31" { TOP.u_full_simulator.u_pipeline.u_execute.u_repne_support.repne_count TOP.u_full_simulator.u_pipeline.u_execute.u_repne_support.count TOP.u_full_simulator.u_pipeline.u_execute.u_repne_support.count_minus_one TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.WB_V TOP.u_full_simulator.u_pipeline.u_execute.u_repne_support.repne_zero_terminate TOP.u_full_simulator.u_pipeline.EX_control_address_debug_out TOP.u_full_simulator.u_pipeline.u_execute.u_operand_select_ex.count TOP.u_full_simulator.u_pipeline.u_execute.u_operand_select_ex.EX_C TOP.u_full_simulator.u_pipeline.u_execute.u_operand_select_ex.saved_count TOP.u_full_simulator.u_pipeline.wb_repne_terminate_all TOP.u_full_simulator.u_pipeline.u_execute.count TOP.u_full_simulator.u_pipeline.u_execute.WB_FLAGS_next }

set _session_group_32 $_session_group_31|
append _session_group_32 u_repne_halt_wb
gui_sg_create "$_session_group_32"
set u_repne_support|u_repne_halt_wb "$_session_group_32"

gui_sg_addsignal -group "$_session_group_32" { TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.wb_halt_all TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.wb_repne_terminate_all TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.CS_IS_HALT_WB TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.CS_IS_CMPS_SECOND_UOP_ALL TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.WB_d2_repne_wb TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.current_flags TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.internal_saved_count TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.ZF TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.zero_count TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.second_uop_of_repne TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.repne_termination_conditions }

set _session_group_33 Group2
gui_sg_create "$_session_group_33"
set Group2 "$_session_group_33"

gui_sg_addsignal -group "$_session_group_33" { TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.final_out_flags TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.CLR TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.PRE TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.v_cs_ld_flags_wb TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.CS_POP_FLAGS_WB TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.CS_FLAGS_AFFECTED_WB TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.WB_FLAGS TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.WB_RESULT_A TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.prev_flags TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.calculated_flags TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.interrupt_flags TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.final_flags TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.and_flags_top TOP.u_full_simulator.u_pipeline.u_writeback.u_flags_wb.and_flags_bottom TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.internal_saved_count TOP.u_full_simulator.u_pipeline.u_lsu_controller.DCACHE_RD_STALL }

set _session_group_34 Group3
gui_sg_create "$_session_group_34"
set Group3 "$_session_group_34"

gui_sg_addsignal -group "$_session_group_34" { TOP.u_full_simulator.u_pipeline.LD_D2 TOP.u_full_simulator.u_pipeline.LD_AG TOP.u_full_simulator.u_pipeline.LD_ME TOP.u_full_simulator.u_pipeline.u_execute.CLK TOP.u_full_simulator.u_pipeline.u_memory_stage2.V TOP.u_full_simulator.u_pipeline.LD_ME2 TOP.u_full_simulator.u_pipeline.EX_control_address_debug TOP.u_full_simulator.u_pipeline.ME2_control_address_debug_out TOP.u_full_simulator.u_pipeline.u_memory_stage2.MEM_RD_ADDR TOP.u_full_simulator.u_pipeline.u_dcache.data_read_out TOP.u_full_simulator.u_pipeline.u_dcache.ready TOP.u_full_simulator.u_pipeline.LSU_OUT_DCACHE_ADDR_IN TOP.u_full_simulator.u_pipeline.u_memory_stage2.A_OUT TOP.u_full_simulator.u_pipeline.u_lsu_controller.DCACHE_RD_DATA TOP.u_full_simulator.u_pipeline.u_lsu_controller.RD_DATA_OUT TOP.u_full_simulator.u_pipeline.LD_EX TOP.u_full_simulator.u_pipeline.u_execute.EX_V TOP.u_full_simulator.u_pipeline.LD_WB TOP.u_full_simulator.u_pipeline.u_writeback.u_repne_halt_wb.WB_V TOP.u_full_simulator.u_pipeline.u_lsu_controller.DCACHE_RD_STALL }

set _session_group_35 $_session_group_34|
append _session_group_35 or_ld_ex
gui_sg_create "$_session_group_35"
set Group3|or_ld_ex "$_session_group_35"

gui_sg_addsignal -group "$_session_group_35" { TOP.u_full_simulator.u_pipeline.or_ld_ex.in0 TOP.u_full_simulator.u_pipeline.or_ld_ex.in1 TOP.u_full_simulator.u_pipeline.or_ld_ex.in2 TOP.u_full_simulator.u_pipeline.u_execute.CLK TOP.u_full_simulator.u_pipeline.or_ld_ex.out TOP.u_full_simulator.u_pipeline.u_execute.EX_A TOP.u_full_simulator.u_pipeline.u_execute.b }

# Global: Highlighting

# Global: Stack
gui_change_stack_mode -mode list

# Post database loading setting...

# Restore C1 time
gui_set_time -C1_only 22281.67



# Save global setting...

# Wave/List view global setting
gui_cov_show_value -switch false

# Close all empty TopLevel windows
foreach __top [gui_ekki_get_window_ids -type TopLevel] {
    if { [llength [gui_ekki_get_window_ids -parent $__top]] == 0} {
        gui_close_window -window $__top
    }
}
gui_set_loading_session_type noSession
# DVE View/pane content session: 


# Hier 'Hier.1'
gui_show_window -window ${Hier.1}
gui_list_set_filter -id ${Hier.1} -list { {Package 1} {All 0} {Process 1} {VirtPowSwitch 0} {UnnamedProcess 1} {UDP 0} {Function 1} {Block 1} {SrsnAndSpaCell 0} {OVA Unit 1} {LeafScCell 1} {LeafVlgCell 1} {Interface 1} {LeafVhdCell 1} {$unit 1} {NamedBlock 1} {Task 1} {VlgPackage 1} {ClassDef 1} {VirtIsoCell 0} }
gui_list_set_filter -id ${Hier.1} -text {*}
gui_hier_list_init -id ${Hier.1}
gui_change_design -id ${Hier.1} -design V1
catch {gui_list_expand -id ${Hier.1} TOP}
catch {gui_list_expand -id ${Hier.1} TOP.u_full_simulator}
catch {gui_list_expand -id ${Hier.1} TOP.u_full_simulator.u_pipeline}
catch {gui_list_select -id ${Hier.1} {TOP.u_full_simulator.u_pipeline.u_lsu_controller}}
gui_view_scroll -id ${Hier.1} -vertical -set 1580
gui_view_scroll -id ${Hier.1} -horizontal -set 0

# Data 'Data.1'
gui_list_set_filter -id ${Data.1} -list { {Buffer 1} {Input 1} {Others 1} {Linkage 1} {Output 1} {LowPower 1} {Parameter 1} {All 1} {Aggregate 1} {LibBaseMember 1} {Event 1} {Assertion 1} {Constant 1} {Interface 1} {BaseMembers 1} {Signal 1} {$unit 1} {Inout 1} {Variable 1} }
gui_list_set_filter -id ${Data.1} -reset
gui_list_show_data -id ${Data.1} {TOP.u_full_simulator.u_pipeline.u_lsu_controller}
gui_show_window -window ${Data.1}
catch { gui_list_select -id ${Data.1} {TOP.u_full_simulator.u_pipeline.u_lsu_controller.DCACHE_RD_STALL TOP.u_full_simulator.u_pipeline.u_lsu_controller.DCACHE_WR_STALL }}
gui_view_scroll -id ${Data.1} -vertical -set 240
gui_view_scroll -id ${Data.1} -horizontal -set 0
gui_view_scroll -id ${Hier.1} -vertical -set 1580
gui_view_scroll -id ${Hier.1} -horizontal -set 0

# Source 'Source.1'
gui_src_value_annotate -id ${Source.1} -switch false
gui_set_env TOGGLE::VALUEANNOTATE 0
gui_open_source -id ${Source.1}  -replace -active TOP.u_full_simulator.u_pipeline.u_lsu_controller ../memory/tlb/lsu.v
gui_view_scroll -id ${Source.1} -vertical -set 216
gui_src_set_reusable -id ${Source.1}

# View 'Wave.1'
gui_wv_sync -id ${Wave.1} -switch false
set groupExD [gui_get_pref_value -category Wave -key exclusiveSG]
gui_set_pref_value -category Wave -key exclusiveSG -value {false}
set origWaveHeight [gui_get_pref_value -category Wave -key waveRowHeight]
gui_list_set_height -id Wave -height 25
set origGroupCreationState [gui_list_create_group_when_add -wave]
gui_list_create_group_when_add -wave -disable
gui_marker_create -id ${Wave.1} C2 22323.67
gui_marker_set_ref -id ${Wave.1}  C1
gui_wv_zoom_timerange -id ${Wave.1} 22213.217 22349.937
gui_list_add_group -id ${Wave.1} -after {New Group} {Group1}
gui_list_add_group -id ${Wave.1} -after {New Group} {u_repne_support}
gui_list_add_group -id ${Wave.1}  -after u_repne_support {u_repne_support|u_repne_halt_wb}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group2}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group3}
gui_list_add_group -id ${Wave.1}  -after Group3 {Group3|or_ld_ex}
gui_list_select -id ${Wave.1} {TOP.u_full_simulator.u_pipeline.u_lsu_controller.DCACHE_RD_DATA }
gui_seek_criteria -id ${Wave.1} {Any Edge}



gui_set_env TOGGLE::DEFAULT_WAVE_WINDOW ${Wave.1}
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
gui_list_set_insertion_bar  -id ${Wave.1} -group Group3  -item {TOP.u_full_simulator.u_pipeline.u_lsu_controller.RD_DATA_OUT[63:0]} -position below

gui_marker_move -id ${Wave.1} {C1} 22281.67
gui_view_scroll -id ${Wave.1} -vertical -set 1520
gui_show_grid -id ${Wave.1} -enable false

# DriverLoad 'DriverLoad.1'
gui_get_drivers -session -id ${DriverLoad.1} -signal {TOP.u_full_simulator.u_pipeline.u_execute.u_repne_support.count[31:0]} -time 19131.52 -starttime 19131.52
gui_get_drivers -session -id ${DriverLoad.1} -signal {TOP.u_full_simulator.u_pipeline.u_writeback.internal_saved_count[31:0]} -time 22393.32 -starttime 22393.82
# Restore toplevel window zorder
# The toplevel window could be closed if it has no view/pane
if {[gui_exist_window -window ${TopLevel.1}]} {
	gui_set_active_window -window ${TopLevel.1}
	gui_set_active_window -window ${Source.1}
}
if {[gui_exist_window -window ${TopLevel.2}]} {
	gui_set_active_window -window ${TopLevel.2}
	gui_set_active_window -window ${Wave.1}
}
#</Session>

