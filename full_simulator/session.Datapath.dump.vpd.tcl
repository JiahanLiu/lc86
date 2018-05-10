# Begin_DVE_Session_Save_Info
# DVE full session
# Saved on Thu May 10 00:41:08 2018
# Designs open: 1
#   V1: pipeline.dump.vpd
# Toplevel windows open: 2
# 	TopLevel.1
# 	TopLevel.2
#   Source.1: TOP.u_full_simulator.u_pipeline.u_memory_stage2
#   Wave.1: 92 signals
#   Group count = 20
#   Group Clocks signal count = 2
#   Group $ to BUS INTERFACE signal count = 2
#   Group FULL MEMORY signal count = 7
#   Group PIPELINE signal count = 0
#   Group ICACHE signal count = 7
#   Group DCACHE signal count = 18
#   Group D2 Stage signal count = 2
#   Group AG Stage signal count = 2
#   Group AG2 Stage signal count = 2
#   Group ME Stage signal count = 2
#   Group ME2 Stage signal count = 5
#   Group EX Stage signal count = 5
#   Group Group7 signal count = 1
#   Group WB Stage signal count = 10
# End_DVE_Session_Save_Info

# DVE version: K-2015.09-SP1_Full64
# DVE build date: Nov 24 2015 21:15:24


#<Session mode="Full" path="/home/ecelrc/students/jliu1/lc86/full_simulator/session.Datapath.dump.vpd.tcl" type="Debug">

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
gui_show_window -window ${TopLevel.1} -show_state normal -rect {{99 84} {1492 938}}

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
set HSPane.1 [gui_create_window -type HSPane -parent ${TopLevel.1} -dock_state left -dock_on_new_line true -dock_extent 421]
catch { set Hier.1 [gui_share_window -id ${HSPane.1} -type Hier] }
gui_set_window_pref_key -window ${HSPane.1} -key dock_width -value_type integer -value 421
gui_set_window_pref_key -window ${HSPane.1} -key dock_height -value_type integer -value 559
gui_set_window_pref_key -window ${HSPane.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${HSPane.1} {{left 0} {top 0} {width 420} {height 562} {dock_state left} {dock_on_new_line true} {child_hier_colhier 235} {child_hier_coltype 195} {child_hier_colpd 0} {child_hier_col1 0} {child_hier_col2 1} {child_hier_col3 -1}}
set Console.1 [gui_create_window -type Console -parent ${TopLevel.1} -dock_state bottom -dock_on_new_line true -dock_extent 179]
gui_set_window_pref_key -window ${Console.1} -key dock_width -value_type integer -value 307
gui_set_window_pref_key -window ${Console.1} -key dock_height -value_type integer -value 179
gui_set_window_pref_key -window ${Console.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${Console.1} {{left 0} {top 0} {width 1393} {height 178} {dock_state bottom} {dock_on_new_line true}}
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
gui_show_window -window ${TopLevel.2} -show_state normal -rect {{274 22} {1667 876}}

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
gui_update_layout -id ${Wave.1} {{show_state maximized} {dock_state undocked} {dock_on_new_line false} {child_wave_left 404} {child_wave_right 984} {child_wave_colname 200} {child_wave_colvalue 200} {child_wave_col1 0} {child_wave_col2 1}}

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
gui_load_child_values {TOP.u_full_simulator.u_pipeline.u_agen_stage2}
gui_load_child_values {TOP.u_full_simulator.u_full_memory.main_memory_u}
gui_load_child_values {TOP.u_full_simulator.u_pipeline.u_icache}
gui_load_child_values {TOP.u_full_simulator.u_full_memory}
gui_load_child_values {TOP.u_full_simulator.u_full_memory.ICACHE_PORT}
gui_load_child_values {TOP.u_full_simulator}
gui_load_child_values {TOP.u_full_simulator.u_pipeline.u_dcache.data_u}
gui_load_child_values {TOP.u_full_simulator.u_full_memory.DCACHE_PORT}
gui_load_child_values {TOP.u_full_simulator.u_pipeline.u_dcache}


set _session_group_1 Clocks
gui_sg_create "$_session_group_1"
set Clocks "$_session_group_1"

gui_sg_addsignal -group "$_session_group_1" { TOP.clk TOP.bus_clk }

set _session_group_2 {$ to BUS INTERFACE}
gui_sg_create "$_session_group_2"
set {$ to BUS INTERFACE} "$_session_group_2"

gui_sg_addsignal -group "$_session_group_2" { }

set _session_group_3 $_session_group_2|
append _session_group_3 DCACHE
gui_sg_create "$_session_group_3"
set {$ to BUS INTERFACE|DCACHE} "$_session_group_3"

gui_sg_addsignal -group "$_session_group_3" { TOP.u_full_simulator.DC_EN TOP.u_full_simulator.DC_WRITE_DATA TOP.u_full_simulator.DC_READ_DATA TOP.u_full_simulator.DC_WR TOP.u_full_simulator.DC_R TOP.u_full_simulator.DC_A }

gui_sg_move "$_session_group_3" -after "$_session_group_2" -pos 1 

set _session_group_4 $_session_group_2|
append _session_group_4 ICACHE
gui_sg_create "$_session_group_4"
set {$ to BUS INTERFACE|ICACHE} "$_session_group_4"

gui_sg_addsignal -group "$_session_group_4" { TOP.u_full_simulator.IC_EN TOP.u_full_simulator.IC_WRITE_DATA TOP.u_full_simulator.IC_READ_DATA TOP.u_full_simulator.IC_WR TOP.u_full_simulator.u_full_memory.IC_R }

set _session_group_5 {FULL MEMORY}
gui_sg_create "$_session_group_5"
set {FULL MEMORY} "$_session_group_5"

gui_sg_addsignal -group "$_session_group_5" { TOP.u_full_simulator.u_full_memory.D TOP.u_full_simulator.u_full_memory.A TOP.u_full_simulator.u_full_memory.SIZE TOP.u_full_simulator.u_full_memory.RW }

set _session_group_6 $_session_group_5|
append _session_group_6 {IC PORT}
gui_sg_create "$_session_group_6"
set {FULL MEMORY|IC PORT} "$_session_group_6"

gui_sg_addsignal -group "$_session_group_6" { TOP.u_full_simulator.u_full_memory.ICACHE_PORT.current_state }

gui_sg_move "$_session_group_6" -after "$_session_group_5" -pos 6 

set _session_group_7 $_session_group_5|
append _session_group_7 {DC PORT}
gui_sg_create "$_session_group_7"
set {FULL MEMORY|DC PORT} "$_session_group_7"

gui_sg_addsignal -group "$_session_group_7" { TOP.u_full_simulator.u_full_memory.DCACHE_PORT.current_state }

gui_sg_move "$_session_group_7" -after "$_session_group_5" -pos 5 

set _session_group_8 $_session_group_5|
append _session_group_8 {Main Memory}
gui_sg_create "$_session_group_8"
set {FULL MEMORY|Main Memory} "$_session_group_8"

gui_sg_addsignal -group "$_session_group_8" { TOP.u_full_simulator.u_full_memory.main_memory_u.ADDR TOP.u_full_simulator.u_full_memory.main_memory_u.WR TOP.u_full_simulator.u_full_memory.main_memory_u.EN TOP.u_full_simulator.u_full_memory.main_memory_u.WRITE_SIZE TOP.u_full_simulator.u_full_memory.main_memory_u.DATA_BUF }

gui_sg_move "$_session_group_8" -after "$_session_group_5" -pos 4 

set _session_group_9 PIPELINE
gui_sg_create "$_session_group_9"
set PIPELINE "$_session_group_9"


set _session_group_10 ICACHE
gui_sg_create "$_session_group_10"
set ICACHE "$_session_group_10"

gui_sg_addsignal -group "$_session_group_10" { TOP.u_full_simulator.u_pipeline.u_icache.current_state TOP.u_full_simulator.u_pipeline.u_icache.RW TOP.u_full_simulator.u_pipeline.u_icache.enable TOP.u_full_simulator.u_pipeline.u_icache.addr TOP.u_full_simulator.u_pipeline.u_icache.size TOP.u_full_simulator.u_pipeline.u_icache.data_read_out TOP.u_full_simulator.u_pipeline.u_icache.ready }

set _session_group_11 DCACHE
gui_sg_create "$_session_group_11"
set DCACHE "$_session_group_11"

gui_sg_addsignal -group "$_session_group_11" { TOP.u_full_simulator.u_pipeline.u_dcache.RW TOP.u_full_simulator.u_pipeline.u_dcache.enable TOP.u_full_simulator.u_pipeline.u_dcache.addr_raw TOP.u_full_simulator.u_pipeline.u_dcache.size TOP.u_full_simulator.u_pipeline.u_dcache.ready TOP.u_full_simulator.u_pipeline.u_dcache.current_state TOP.u_full_simulator.u_pipeline.u_dcache.evict TOP.u_full_simulator.u_pipeline.u_dcache.HIT TOP.u_full_simulator.u_pipeline.u_dcache.OE TOP.u_full_simulator.u_pipeline.u_dcache.CACHE_WR TOP.u_full_simulator.u_pipeline.u_dcache.TS_WR TOP.u_full_simulator.u_pipeline.u_dcache.d_mux TOP.u_full_simulator.u_pipeline.u_dcache.tagstore_V TOP.u_full_simulator.u_pipeline.u_dcache.tagstore_D TOP.u_full_simulator.u_pipeline.u_dcache.tagstore_tag TOP.u_full_simulator.u_pipeline.u_dcache.MATCH TOP.u_full_simulator.u_pipeline.u_dcache.INVALID }

set _session_group_12 $_session_group_11|
append _session_group_12 data_u
gui_sg_create "$_session_group_12"
set DCACHE|data_u "$_session_group_12"

gui_sg_addsignal -group "$_session_group_12" { TOP.u_full_simulator.u_pipeline.u_dcache.data_u.A TOP.u_full_simulator.u_pipeline.u_dcache.data_u.DIN TOP.u_full_simulator.u_pipeline.u_dcache.data_u.OE TOP.u_full_simulator.u_pipeline.u_dcache.data_u.WR TOP.u_full_simulator.u_pipeline.u_dcache.data_u.DOUT TOP.u_full_simulator.u_pipeline.u_dcache.data_u.DOUT_ARRAY TOP.u_full_simulator.u_pipeline.u_dcache.data_u.DOUT_ARRAY0 TOP.u_full_simulator.u_pipeline.u_dcache.data_u.DOUT_ARRAY1 TOP.u_full_simulator.u_pipeline.u_dcache.data_u.DOUT_ARRAY2 TOP.u_full_simulator.u_pipeline.u_dcache.data_u.DOUT_ARRAY3 TOP.u_full_simulator.u_pipeline.u_dcache.data_u.a_dec TOP.u_full_simulator.u_pipeline.u_dcache.data_u.a_dec_inv TOP.u_full_simulator.u_pipeline.u_dcache.data_u.wr0 TOP.u_full_simulator.u_pipeline.u_dcache.data_u.wr1 TOP.u_full_simulator.u_pipeline.u_dcache.data_u.wr2 TOP.u_full_simulator.u_pipeline.u_dcache.data_u.wr3 }

set _session_group_13 {D2 Stage}
gui_sg_create "$_session_group_13"
set {D2 Stage} "$_session_group_13"

gui_sg_addsignal -group "$_session_group_13" { TOP.u_full_simulator.u_pipeline.D2_control_address_debug TOP.u_full_simulator.u_pipeline.u_decode_stage2.D2_V }

set _session_group_14 {AG Stage}
gui_sg_create "$_session_group_14"
set {AG Stage} "$_session_group_14"

gui_sg_addsignal -group "$_session_group_14" { TOP.u_full_simulator.u_pipeline.AG_control_address_debug TOP.u_full_simulator.u_pipeline.u_agen_stage1.V }

set _session_group_15 {AG2 Stage}
gui_sg_create "$_session_group_15"
set {AG2 Stage} "$_session_group_15"

gui_sg_addsignal -group "$_session_group_15" { TOP.u_full_simulator.u_pipeline.AG2_control_address_debug TOP.u_full_simulator.u_pipeline.u_agen_stage2.V }

set _session_group_16 {ME Stage}
gui_sg_create "$_session_group_16"
set {ME Stage} "$_session_group_16"

gui_sg_addsignal -group "$_session_group_16" { TOP.u_full_simulator.u_pipeline.ME_control_address_debug TOP.u_full_simulator.u_pipeline.u_memory_stage1.V }

set _session_group_17 {ME2 Stage}
gui_sg_create "$_session_group_17"
set {ME2 Stage} "$_session_group_17"

gui_sg_addsignal -group "$_session_group_17" { TOP.u_full_simulator.u_pipeline.ME2_control_address_debug TOP.u_full_simulator.u_pipeline.u_memory_stage2.V TOP.u_full_simulator.u_pipeline.u_memory_stage2.A_OUT TOP.u_full_simulator.u_pipeline.u_memory_stage2.B_OUT TOP.u_full_simulator.u_pipeline.u_memory_stage2.MEM_RD_ADDR }

set _session_group_18 {EX Stage}
gui_sg_create "$_session_group_18"
set {EX Stage} "$_session_group_18"

gui_sg_addsignal -group "$_session_group_18" { TOP.u_full_simulator.u_pipeline.EX_control_address_debug TOP.u_full_simulator.u_pipeline.u_execute.EX_V TOP.u_full_simulator.u_pipeline.u_execute.EX_A TOP.u_full_simulator.u_pipeline.u_execute.b TOP.u_full_simulator.u_pipeline.u_execute.WB_FLAGS_next }

set _session_group_19 Group7
gui_sg_create "$_session_group_19"
set Group7 "$_session_group_19"

gui_sg_addsignal -group "$_session_group_19" { TOP.u_full_simulator.u_pipeline.WB_control_address_debug }

set _session_group_20 {WB Stage}
gui_sg_create "$_session_group_20"
set {WB Stage} "$_session_group_20"

gui_sg_addsignal -group "$_session_group_20" { TOP.u_full_simulator.u_pipeline.WB_control_address_debug TOP.u_full_simulator.u_pipeline.u_writeback.WB_V TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_gpr1 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_data1 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_gpr2 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_data2 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_gpr3 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_data3 TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_ld_flags TOP.u_full_simulator.u_pipeline.u_writeback.WB_Final_Flags }

# Global: Highlighting

# Global: Stack
gui_change_stack_mode -mode list

# Post database loading setting...

# Restore C1 time
gui_set_time -C1_only 4151.025



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
gui_list_set_filter -id ${Hier.1} -text {*memory*}
gui_hier_list_init -id ${Hier.1}
gui_change_design -id ${Hier.1} -design V1
catch {gui_list_expand -id ${Hier.1} TOP}
catch {gui_list_expand -id ${Hier.1} TOP.u_full_simulator}
catch {gui_list_expand -id ${Hier.1} TOP.u_full_simulator.u_pipeline}
catch {gui_list_select -id ${Hier.1} {TOP.u_full_simulator.u_pipeline.u_memory_stage2}}
gui_view_scroll -id ${Hier.1} -vertical -set 286
gui_view_scroll -id ${Hier.1} -horizontal -set 0

# Source 'Source.1'
gui_src_value_annotate -id ${Source.1} -switch false
gui_set_env TOGGLE::VALUEANNOTATE 0
gui_open_source -id ${Source.1}  -replace -active TOP.u_full_simulator.u_pipeline.u_memory_stage2 ../pipeline/memory_stage2.v
gui_view_scroll -id ${Source.1} -vertical -set 42
gui_src_set_reusable -id ${Source.1}

# View 'Wave.1'
gui_wv_sync -id ${Wave.1} -switch false
set groupExD [gui_get_pref_value -category Wave -key exclusiveSG]
gui_set_pref_value -category Wave -key exclusiveSG -value {false}
set origWaveHeight [gui_get_pref_value -category Wave -key waveRowHeight]
gui_list_set_height -id Wave -height 25
set origGroupCreationState [gui_list_create_group_when_add -wave]
gui_list_create_group_when_add -wave -disable
gui_marker_set_ref -id ${Wave.1}  C1
gui_wv_zoom_timerange -id ${Wave.1} 3450.605 5728.95
gui_list_add_group -id ${Wave.1} -after {New Group} {Clocks}
gui_list_add_group -id ${Wave.1} -after {New Group} {{$ to BUS INTERFACE}}
gui_list_add_group -id ${Wave.1}  -after {$ to BUS INTERFACE} {{$ to BUS INTERFACE|ICACHE}}
gui_list_add_group -id ${Wave.1} -after {$ to BUS INTERFACE|ICACHE} {{$ to BUS INTERFACE|DCACHE}}
gui_list_add_group -id ${Wave.1} -after {New Group} {{FULL MEMORY}}
gui_list_add_group -id ${Wave.1}  -after TOP.u_full_simulator.u_full_memory.RW {{FULL MEMORY|Main Memory}}
gui_list_add_group -id ${Wave.1} -after {FULL MEMORY|Main Memory} {{FULL MEMORY|DC PORT}}
gui_list_add_group -id ${Wave.1} -after {FULL MEMORY|DC PORT} {{FULL MEMORY|IC PORT}}
gui_list_add_group -id ${Wave.1} -after {New Group} {PIPELINE}
gui_list_add_group -id ${Wave.1} -after {New Group} {ICACHE}
gui_list_add_group -id ${Wave.1} -after {New Group} {DCACHE}
gui_list_add_group -id ${Wave.1}  -after DCACHE {DCACHE|data_u}
gui_list_add_group -id ${Wave.1} -after {New Group} {{D2 Stage}}
gui_list_add_group -id ${Wave.1} -after {New Group} {{AG Stage}}
gui_list_add_group -id ${Wave.1} -after {New Group} {{AG2 Stage}}
gui_list_add_group -id ${Wave.1} -after {New Group} {{ME Stage}}
gui_list_add_group -id ${Wave.1} -after {New Group} {{ME2 Stage}}
gui_list_add_group -id ${Wave.1} -after {New Group} {{EX Stage}}
gui_list_add_group -id ${Wave.1} -after {New Group} {{WB Stage}}
gui_list_collapse -id ${Wave.1} {$ to BUS INTERFACE}
gui_list_collapse -id ${Wave.1} {FULL MEMORY|Main Memory}
gui_list_collapse -id ${Wave.1} ICACHE
gui_list_collapse -id ${Wave.1} DCACHE
gui_list_select -id ${Wave.1} {TOP.u_full_simulator.u_pipeline.u_memory_stage2.A_OUT TOP.u_full_simulator.u_pipeline.u_memory_stage2.B_OUT TOP.u_full_simulator.u_pipeline.u_memory_stage2.MEM_RD_ADDR }
gui_seek_criteria -id ${Wave.1} {Any Edge}

gui_list_alias -id ${Wave.1} -group ${FULL MEMORY|DC PORT} -index 0 -signal V1:TOP.u_full_simulator.u_full_memory.DCACHE_PORT.current_state -add DC_PORT_STATE 
gui_list_alias -id ${Wave.1} -group ${ICACHE} -index 0 -signal V1:TOP.u_full_simulator.u_pipeline.u_icache.current_state -add IC_STATE 


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
gui_list_set_insertion_bar  -id ${Wave.1} -group {ME2 Stage}  -item {TOP.u_full_simulator.u_pipeline.u_memory_stage2.MEM_RD_ADDR[31:0]} -position below

gui_marker_move -id ${Wave.1} {C1} 4151.025
gui_view_scroll -id ${Wave.1} -vertical -set 605
gui_show_grid -id ${Wave.1} -enable false
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

