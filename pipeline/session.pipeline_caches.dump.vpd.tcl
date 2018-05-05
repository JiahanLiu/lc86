# Begin_DVE_Session_Save_Info
# DVE full session
# Saved on Sat May 5 18:25:54 2018
# Designs open: 1
#   V1: pipeline.dump.vpd
# Toplevel windows open: 4
# 	TopLevel.1
# 	TopLevel.2
# 	TopLevel.3
# 	TopLevel.4
#   Source.1: TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3
#   Wave.1: 142 signals
#   Wave.2: 54 signals
#   Wave.3: 306 signals
#   Group count = 19
#   Group Group1 signal count = 1
#   Group Group2 signal count = 25
#   Group Group3 signal count = 12
#   Group Group4 signal count = 1
#   Group Group5 signal count = 1
#   Group Group6 signal count = 8
#   Group Group7 signal count = 1
#   Group Group8 signal count = 18
#   Group Group9 signal count = 6
#   Group Group10 signal count = 3
#   Group Group11 signal count = 27
#   Group Group12 signal count = 1
#   Group u_pipeline signal count = 768
#   Group u_reg_dependency_check signal count = 67
# End_DVE_Session_Save_Info

# DVE version: K-2015.09-SP1_Full64
# DVE build date: Nov 24 2015 21:15:24


#<Session mode="Full" path="/home/ecelrc/students/anarkhede/micro/lc86/pipeline/session.pipeline_caches.dump.vpd.tcl" type="Debug">

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
gui_show_window -window ${TopLevel.1} -show_state normal -rect {{378 191} {1968 1032}}

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
set HSPane.1 [gui_create_window -type HSPane -parent ${TopLevel.1} -dock_state left -dock_on_new_line true -dock_extent 185]
catch { set Hier.1 [gui_share_window -id ${HSPane.1} -type Hier] }
gui_set_window_pref_key -window ${HSPane.1} -key dock_width -value_type integer -value 185
gui_set_window_pref_key -window ${HSPane.1} -key dock_height -value_type integer -value -1
gui_set_window_pref_key -window ${HSPane.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${HSPane.1} {{left 0} {top 0} {width 184} {height 558} {dock_state left} {dock_on_new_line true} {child_hier_colhier 140} {child_hier_coltype 100} {child_hier_colpd 0} {child_hier_col1 0} {child_hier_col2 1} {child_hier_col3 -1}}
set DLPane.1 [gui_create_window -type DLPane -parent ${TopLevel.1} -dock_state left -dock_on_new_line true -dock_extent 326]
catch { set Data.1 [gui_share_window -id ${DLPane.1} -type Data] }
gui_set_window_pref_key -window ${DLPane.1} -key dock_width -value_type integer -value 326
gui_set_window_pref_key -window ${DLPane.1} -key dock_height -value_type integer -value 584
gui_set_window_pref_key -window ${DLPane.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${DLPane.1} {{left 0} {top 0} {width 325} {height 558} {dock_state left} {dock_on_new_line true} {child_data_colvariable 182} {child_data_colvalue 100} {child_data_coltype 56} {child_data_col1 0} {child_data_col2 1} {child_data_col3 2}}
set Console.1 [gui_create_window -type Console -parent ${TopLevel.1} -dock_state bottom -dock_on_new_line true -dock_extent 151]
gui_set_window_pref_key -window ${Console.1} -key dock_width -value_type integer -value -1
gui_set_window_pref_key -window ${Console.1} -key dock_height -value_type integer -value 151
gui_set_window_pref_key -window ${Console.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${Console.1} {{left 0} {top 0} {width 295} {height 179} {dock_state bottom} {dock_on_new_line true}}
set DriverLoad.1 [gui_create_window -type DriverLoad -parent ${TopLevel.1} -dock_state bottom -dock_on_new_line false -dock_extent 180]
gui_set_window_pref_key -window ${DriverLoad.1} -key dock_width -value_type integer -value 150
gui_set_window_pref_key -window ${DriverLoad.1} -key dock_height -value_type integer -value 180
gui_set_window_pref_key -window ${DriverLoad.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${DriverLoad.1} {{left 0} {top 0} {width 1294} {height 179} {dock_state bottom} {dock_on_new_line false}}
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
gui_show_window -window ${TopLevel.2} -show_state normal -rect {{333 81} {2002 909}}

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
gui_update_layout -id ${Wave.1} {{show_state maximized} {dock_state undocked} {dock_on_new_line false} {child_wave_left 484} {child_wave_right 1180} {child_wave_colname 208} {child_wave_colvalue 272} {child_wave_col1 0} {child_wave_col2 1}}

# End MDI window settings


# Create and position top-level window: TopLevel.3

if {![gui_exist_window -window TopLevel.3]} {
    set TopLevel.3 [ gui_create_window -type TopLevel \
       -icon $::env(DVE)/auxx/gui/images/toolbars/dvewin.xpm] 
} else { 
    set TopLevel.3 TopLevel.3
}
gui_show_window -window ${TopLevel.3} -show_state normal -rect {{383 244} {1835 923}}

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
gui_sync_global -id ${TopLevel.3} -option true

# MDI window settings
set Wave.2 [gui_create_window -type {Wave}  -parent ${TopLevel.3}]
gui_show_window -window ${Wave.2} -show_state maximized
gui_update_layout -id ${Wave.2} {{show_state maximized} {dock_state undocked} {dock_on_new_line false} {child_wave_left 421} {child_wave_right 1026} {child_wave_colname 208} {child_wave_colvalue 209} {child_wave_col1 0} {child_wave_col2 1}}

# End MDI window settings


# Create and position top-level window: TopLevel.4

if {![gui_exist_window -window TopLevel.4]} {
    set TopLevel.4 [ gui_create_window -type TopLevel \
       -icon $::env(DVE)/auxx/gui/images/toolbars/dvewin.xpm] 
} else { 
    set TopLevel.4 TopLevel.4
}
gui_show_window -window ${TopLevel.4} -show_state normal -rect {{403 255} {1855 934}}

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
gui_sync_global -id ${TopLevel.4} -option true

# MDI window settings
set Wave.3 [gui_create_window -type {Wave}  -parent ${TopLevel.4}]
gui_show_window -window ${Wave.3} -show_state maximized
gui_update_layout -id ${Wave.3} {{show_state maximized} {dock_state undocked} {dock_on_new_line false} {child_wave_left 421} {child_wave_right 1026} {child_wave_colname 208} {child_wave_colvalue 209} {child_wave_col1 0} {child_wave_col2 1}}

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
gui_update_statusbar_target_frame ${TopLevel.3}
gui_update_statusbar_target_frame ${TopLevel.4}

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
gui_load_child_values {TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1}
gui_load_child_values {TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2}
gui_load_child_values {TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3}
gui_load_child_values {TOP.u_pipeline.u_icache.gen_n_state_u}
gui_load_child_values {TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4}
gui_load_child_values {TOP.u_pipeline.u_agen_stage1}
gui_load_child_values {TOP.u_pipeline.u_execute}
gui_load_child_values {TOP.u_pipeline.u_icache}
gui_load_child_values {TOP.u_pipeline.u_decode_stage2}
gui_load_child_values {TOP.u_pipeline.u_icache.tagstore_u}
gui_load_child_values {TOP.u_pipeline.u_fetch}
gui_load_child_values {TOP.u_pipeline}
gui_load_child_values {TOP.u_pipeline.u_register_file}
gui_load_child_values {TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check}


set _session_group_112 Group1
gui_sg_create "$_session_group_112"
set Group1 "$_session_group_112"

gui_sg_addsignal -group "$_session_group_112" { TOP.u_pipeline.CLK }

set _session_group_113 Group2
gui_sg_create "$_session_group_113"
set Group2 "$_session_group_113"

gui_sg_addsignal -group "$_session_group_113" { TOP.u_pipeline.CLK TOP.u_pipeline.u_decode_stage2.offset TOP.u_pipeline.u_decode_stage2.CONTROL_STORE TOP.u_pipeline.u_decode_stage2.D2_SR1_NEEDED_AG TOP.u_pipeline.u_decode_stage2.D2_SEG1_NEEDED_AG TOP.u_pipeline.u_decode_stage2.D2_MM1_NEEDED_AG TOP.u_pipeline.u_decode_stage2.D2_MEM_RD_ME TOP.u_pipeline.u_decode_stage2.D2_MEM_WR_ME TOP.u_pipeline.u_decode_stage2.D2_ALUK_EX TOP.u_pipeline.u_decode_stage2.D2_LD_GPR1_WB TOP.u_pipeline.u_decode_stage2.D2_LD_MM_WB TOP.u_pipeline.u_decode_stage2.SR1_OUT TOP.u_pipeline.u_decode_stage2.SR2_OUT TOP.u_pipeline.u_decode_stage2.SR3_OUT TOP.u_pipeline.u_decode_stage2.SR4_OUT TOP.u_pipeline.u_decode_stage2.SEG1_OUT TOP.u_pipeline.u_decode_stage2.SEG2_OUT TOP.u_pipeline.u_decode_stage2.IMM32_OUT TOP.u_pipeline.u_decode_stage2.DISP32_OUT TOP.u_pipeline.u_decode_stage2.DE_SIB_EN_AG TOP.u_pipeline.u_decode_stage2.DE_DISP_EN_AG TOP.u_pipeline.u_decode_stage2.DE_BASE_REG_EN_AG TOP.u_pipeline.u_decode_stage2.DE_MUX_SEG_AG TOP.u_pipeline.u_decode_stage2.DE_CMPXCHG_AG TOP.u_pipeline.u_decode_stage2.DE_SIB_S_AG }

set _session_group_114 Group3
gui_sg_create "$_session_group_114"
set Group3 "$_session_group_114"

gui_sg_addsignal -group "$_session_group_114" { TOP.u_pipeline.CLK TOP.u_pipeline.SR1_DATA TOP.u_pipeline.SR2_DATA TOP.u_pipeline.SR3_DATA TOP.u_pipeline.SIB_I_DATA TOP.u_pipeline.u_register_file.SEGDOUT1 TOP.u_pipeline.u_register_file.SEGDOUT2 TOP.u_pipeline.u_register_file.MMDOUT1 TOP.u_pipeline.u_register_file.MMDOUT2 TOP.u_pipeline.u_register_file.CSDOUT TOP.u_pipeline.u_register_file.EIPDOUT TOP.u_pipeline.u_register_file.EFLAGSDOUT }

set _session_group_115 Group4
gui_sg_create "$_session_group_115"
set Group4 "$_session_group_115"

gui_sg_addsignal -group "$_session_group_115" { TOP.u_pipeline.CLK }

set _session_group_116 Group5
gui_sg_create "$_session_group_116"
set Group5 "$_session_group_116"

gui_sg_addsignal -group "$_session_group_116" { TOP.u_pipeline.CLK }

set _session_group_117 Group6
gui_sg_create "$_session_group_117"
set Group6 "$_session_group_117"

gui_sg_addsignal -group "$_session_group_117" { TOP.u_pipeline.CLK TOP.u_pipeline.u_execute.WB_V_next TOP.u_pipeline.u_execute.WB_NEIP_next TOP.u_pipeline.u_execute.WB_NCS_next TOP.u_pipeline.u_execute.WB_CONTROL_STORE_next TOP.u_pipeline.u_execute.WB_FLAGS_next TOP.u_pipeline.u_execute.WB_DR1_next TOP.u_pipeline.u_execute.WB_DR2_next }

set _session_group_118 Group7
gui_sg_create "$_session_group_118"
set Group7 "$_session_group_118"

gui_sg_addsignal -group "$_session_group_118" { TOP.u_pipeline.CLK }

set _session_group_119 Group8
gui_sg_create "$_session_group_119"
set Group8 "$_session_group_119"

gui_sg_addsignal -group "$_session_group_119" { TOP.u_pipeline.u_icache.CLK TOP.u_pipeline.u_icache.SET TOP.u_pipeline.u_icache.RST TOP.u_pipeline.u_icache.data_write TOP.u_pipeline.u_icache.RW TOP.u_pipeline.u_icache.enable TOP.u_pipeline.u_icache.addr TOP.u_pipeline.u_icache.size TOP.u_pipeline.u_icache.data_read TOP.u_pipeline.u_icache.ready TOP.u_pipeline.u_icache.BUS_WR TOP.u_pipeline.u_icache.BUS_EN TOP.u_pipeline.u_icache.BUS_ADDR TOP.u_pipeline.u_icache.BUS_WRITE TOP.u_pipeline.u_icache.BUS_R TOP.u_pipeline.u_icache.BUS_READ TOP.u_pipeline.u_icache.current_state TOP.u_pipeline.u_icache.tagstore_u.valid_out }

set _session_group_120 Group9
gui_sg_create "$_session_group_120"
set Group9 "$_session_group_120"

gui_sg_addsignal -group "$_session_group_120" { TOP.u_pipeline.u_icache.gen_n_state_u.current_state TOP.u_pipeline.u_icache.gen_n_state_u.enable TOP.u_pipeline.u_icache.gen_n_state_u.RW TOP.u_pipeline.u_icache.gen_n_state_u.HIT TOP.u_pipeline.u_icache.gen_n_state_u.BUS_R TOP.u_pipeline.u_icache.gen_n_state_u.EV }

set _session_group_121 Group10
gui_sg_create "$_session_group_121"
set Group10 "$_session_group_121"

gui_sg_addsignal -group "$_session_group_121" { TOP.u_pipeline.u_fetch.IR_OUT TOP.u_pipeline.u_fetch.instr_length_updt TOP.u_pipeline.u_fetch.opcode }

set _session_group_122 Group11
gui_sg_create "$_session_group_122"
set Group11 "$_session_group_122"

gui_sg_addsignal -group "$_session_group_122" { TOP.u_pipeline.D2_V TOP.u_pipeline.u_fetch.CLK TOP.u_pipeline.AG_DEP_STALL_OUT TOP.u_pipeline.u_agen_stage1.reg_dep_stall_out TOP.u_pipeline.u_agen_stage1.dep_df_stall TOP.u_pipeline.AG_PS_V TOP.u_pipeline.AG2_PS_V TOP.u_pipeline.ME_PS_V TOP.u_pipeline.ME2_PS_V TOP.u_pipeline.EX_V TOP.u_pipeline.WB_V TOP.u_pipeline.AG_GPR_SCOREBOARD_OUT TOP.u_pipeline.AG2_GPR_SCOREBOARD_OUT TOP.u_pipeline.ME_GPR_SCOREBOARD_OUT TOP.u_pipeline.ME2_GPR_SCOREBOARD_OUT TOP.u_pipeline.EX_GPR_SCOREBOARD_OUT TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.DEP_STALL TOP.u_pipeline.u_fetch.rst_state TOP.u_pipeline.u_fetch.flush_state TOP.u_pipeline.u_fetch.exc_state TOP.u_pipeline.u_fetch.fill_state TOP.u_pipeline.u_fetch.empty_state TOP.u_pipeline.u_fetch.full_state }

set _session_group_123 $_session_group_122|
append _session_group_123 u_gpr_scoreboard_check_sr4
gui_sg_create "$_session_group_123"
set Group11|u_gpr_scoreboard_check_sr4 "$_session_group_123"

gui_sg_addsignal -group "$_session_group_123" { TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.V TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.REG_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.REG TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.SIZE TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.STALL TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.sb7 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.sb6 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.sb5 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.sb4 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.sb3 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.sb2 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.sb1 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.sb0 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.mux0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.or0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.or1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.or2_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.and0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.and1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.mux1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.reg_sel TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr4.mux2_out }

gui_sg_move "$_session_group_123" -after "$_session_group_122" -pos 20 

set _session_group_124 $_session_group_122|
append _session_group_124 u_gpr_scoreboard_check_sr3
gui_sg_create "$_session_group_124"
set Group11|u_gpr_scoreboard_check_sr3 "$_session_group_124"

gui_sg_addsignal -group "$_session_group_124" { TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.V TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.REG_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.REG TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.SIZE TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.STALL TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.sb7 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.sb6 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.sb5 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.sb4 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.sb3 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.sb2 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.sb1 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.sb0 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.mux0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.or0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.or1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.or2_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.and0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.and1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.mux1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.reg_sel TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3.mux2_out }

gui_sg_move "$_session_group_124" -after "$_session_group_122" -pos 19 

set _session_group_125 $_session_group_122|
append _session_group_125 u_gpr_scoreboard_check_sr2
gui_sg_create "$_session_group_125"
set Group11|u_gpr_scoreboard_check_sr2 "$_session_group_125"

gui_sg_addsignal -group "$_session_group_125" { TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.V TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.REG_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.REG TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.SIZE TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.STALL TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.sb7 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.sb6 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.sb5 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.sb4 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.sb3 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.sb2 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.sb1 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.sb0 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.mux0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.or0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.or1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.or2_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.and0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.and1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.mux1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.reg_sel TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr2.mux2_out }

gui_sg_move "$_session_group_125" -after "$_session_group_122" -pos 18 

set _session_group_126 $_session_group_122|
append _session_group_126 u_gpr_scoreboard_check_sr1
gui_sg_create "$_session_group_126"
set Group11|u_gpr_scoreboard_check_sr1 "$_session_group_126"

gui_sg_addsignal -group "$_session_group_126" { TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.V TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.REG_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.REG TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.SIZE TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.STALL TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.sb7 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.sb6 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.sb5 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.sb4 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.sb3 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.sb2 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.sb1 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.sb0 TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.mux0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.or0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.or1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.or2_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.and0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.and1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.mux1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.reg_sel TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr1.mux2_out }

gui_sg_move "$_session_group_126" -after "$_session_group_122" -pos 17 

set _session_group_127 Group12
gui_sg_create "$_session_group_127"
set Group12 "$_session_group_127"

gui_sg_addsignal -group "$_session_group_127" { TOP.u_pipeline.WB_V }

set _session_group_128 u_pipeline
gui_sg_create "$_session_group_128"
set u_pipeline "$_session_group_128"

gui_sg_addsignal -group "$_session_group_128" { TOP.u_pipeline.CLR TOP.u_pipeline.PRE TOP.u_pipeline.IR TOP.u_pipeline.EN TOP.u_pipeline.WB_ld_latches TOP.u_pipeline.DEP_v_ex_ld_gpr1 TOP.u_pipeline.DEP_v_ex_ld_gpr2 TOP.u_pipeline.DEP_v_ex_ld_gpr3 TOP.u_pipeline.Dep_v_ex_ld_seg TOP.u_pipeline.Dep_v_ex_ld_mm TOP.u_pipeline.Dep_v_ex_dcache_write TOP.u_pipeline.DEP_v_wb_ld_gpr1 TOP.u_pipeline.DEP_v_wb_ld_gpr2 TOP.u_pipeline.DEP_v_wb_ld_gpr3 TOP.u_pipeline.DEP_v_wb_ld_seg TOP.u_pipeline.DEP_v_wb_ld_mm TOP.u_pipeline.DEP_v_wb_dcache_write TOP.u_pipeline.WB_Final_DR1 TOP.u_pipeline.WB_Final_DR2 TOP.u_pipeline.WB_Final_DR3 TOP.u_pipeline.WB_Final_data1 TOP.u_pipeline.WB_Final_data2 TOP.u_pipeline.WB_Final_data3 TOP.u_pipeline.WB_Final_ld_gpr1 TOP.u_pipeline.WB_Final_ld_gpr2 TOP.u_pipeline.WB_Final_ld_gpr3 TOP.u_pipeline.WB_Final_datasize TOP.u_pipeline.WB_Final_DR3_datasize TOP.u_pipeline.WB_Final_ld_seg TOP.u_pipeline.WB_Final_MM_Data TOP.u_pipeline.WB_Final_ld_mm TOP.u_pipeline.WB_Final_CS TOP.u_pipeline.WB_Final_ld_cs TOP.u_pipeline.WB_Final_EIP TOP.u_pipeline.WB_Final_ld_eip TOP.u_pipeline.WB_Final_Flags TOP.u_pipeline.WB_Final_ld_flags TOP.u_pipeline.WB_Final_Dcache_Data TOP.u_pipeline.WB_Final_Dcache_address TOP.u_pipeline.WB_Final_Dcache_Write TOP.u_pipeline.In_write_ready TOP.u_pipeline.wb_halt_all TOP.u_pipeline.wb_repne_terminate_all TOP.u_pipeline.WB_stall TOP.u_pipeline.flags_dataforwarded TOP.u_pipeline.count_dataforwarded TOP.u_pipeline.wb_mispredict_taken_all TOP.u_pipeline.WB_EXC_V_OUT TOP.u_pipeline.WB_FLUSH_PIPELINE_BAR TOP.u_pipeline.INTERRUPT_SIGNAL TOP.u_pipeline.WB_GEN_PROT_EXC_EXIST_V TOP.u_pipeline.WB_PAGE_FAULT_EXC_EXIST_V TOP.u_pipeline.JMP_FLUSH TOP.u_pipeline.JMP_FLUSH_BAR TOP.u_pipeline.RST TOP.u_pipeline.AG_DEP_STALL_OUT TOP.u_pipeline.SEG_DIN TOP.u_pipeline.SEGID1 TOP.u_pipeline.SEGID2 TOP.u_pipeline.SEGWE TOP.u_pipeline.MM_DIN TOP.u_pipeline.MMID1 TOP.u_pipeline.MMID2 TOP.u_pipeline.WRMMID TOP.u_pipeline.MMWE TOP.u_pipeline.GPR_DIN0 TOP.u_pipeline.GPR_DIN1 TOP.u_pipeline.GPR_DIN2 TOP.u_pipeline.GPRID0 TOP.u_pipeline.GPRID1 TOP.u_pipeline.GPRID2 TOP.u_pipeline.GPRID3 TOP.u_pipeline.WRGPR0 TOP.u_pipeline.WRGPR1 TOP.u_pipeline.WRGPR2 TOP.u_pipeline.GPR_RE0 TOP.u_pipeline.GPR_RE1 TOP.u_pipeline.GPR_RE2 TOP.u_pipeline.GPR_RE3 TOP.u_pipeline.GPRWE0 TOP.u_pipeline.GPRWE1 TOP.u_pipeline.GPRWE2 TOP.u_pipeline.WE0 TOP.u_pipeline.WE1 TOP.u_pipeline.WE2 TOP.u_pipeline.CS_DIN TOP.u_pipeline.EIP_DIN TOP.u_pipeline.EFLAGS_DIN TOP.u_pipeline.LD_CS TOP.u_pipeline.LD_EIP TOP.u_pipeline.LD_EFLAGS TOP.u_pipeline.SEGDOUT1 TOP.u_pipeline.SEGDOUT2 TOP.u_pipeline.MMDOUT1 TOP.u_pipeline.MMDOUT2 TOP.u_pipeline.GPRDOUT0 TOP.u_pipeline.GPRDOUT1 TOP.u_pipeline.GPRDOUT2 TOP.u_pipeline.GPRDOUT3 TOP.u_pipeline.CSDOUT TOP.u_pipeline.EIPDOUT TOP.u_pipeline.EFLAGSDOUT TOP.u_pipeline.SEG1_DATA TOP.u_pipeline.SEG2_DATA TOP.u_pipeline.MM1_DATA TOP.u_pipeline.MM2_DATA TOP.u_pipeline.REG_SEG1_ID TOP.u_pipeline.REG_SEG2_ID TOP.u_pipeline.REG_MM1_ID TOP.u_pipeline.REG_MM2_ID TOP.u_pipeline.REG_SR1_ID TOP.u_pipeline.REG_SR2_ID TOP.u_pipeline.REG_SR3_ID TOP.u_pipeline.REG_SR4_ID TOP.u_pipeline.REG_SR1_SIZE TOP.u_pipeline.REG_SR2_SIZE TOP.u_pipeline.REG_SR3_SIZE TOP.u_pipeline.REG_SR4_SIZE TOP.u_pipeline.ICACHE_DOUT TOP.u_pipeline.FE_ICACHE_PADDR_OUT TOP.u_pipeline.FE_ICACHE_EN_OUT TOP.u_pipeline.ICACHE_READY TOP.u_pipeline.FE_ICACHE_RD_SIZE_OUT TOP.u_pipeline.ICACHE_BUS_WR_OUT TOP.u_pipeline.ICACHE_BUS_EN_OUT TOP.u_pipeline.ICACHE_BUS_ADDR_OUT TOP.u_pipeline.ICACHE_BUS_WRITE_OUT TOP.u_pipeline.BUS_READY TOP.u_pipeline.BUS_READ_DATA TOP.u_pipeline.DCACHE_RD_DATA_OUT_LSU_IN TOP.u_pipeline.DCACHE_READY_LSU_IN TOP.u_pipeline.DCACHE_BUS_WR_OUT TOP.u_pipeline.DCACHE_BUS_EN_OUT TOP.u_pipeline.DCACHE_BUS_ADDR_OUT TOP.u_pipeline.DCACHE_BUS_WRITE_OUT TOP.u_pipeline.LSU_OUT_DCACHE_ADDR_IN TOP.u_pipeline.LSU_OUT_DCACHE_SIZE_IN TOP.u_pipeline.LSU_OUT_DCACHE_RW_IN TOP.u_pipeline.LSU_OUT_DCACHE_EN TOP.u_pipeline.LSU_OUT_DCACHE_WR_DATA_IN TOP.u_pipeline.LSU_OUT_RD_STALL TOP.u_pipeline.LSU_OUT_RD_STALL_BAR TOP.u_pipeline.LSU_OUT_WR_STALL }
gui_sg_addsignal -group "$_session_group_128" { TOP.u_pipeline.LSU_OUT_RD_DATA TOP.u_pipeline.WB_V_LSU_IN TOP.u_pipeline.WB_MEM_WR_LSU_IN TOP.u_pipeline.WB_WR_ADDR1_V_LSU_IN TOP.u_pipeline.WB_WR_ADDR2_V_LSU_IN TOP.u_pipeline.WB_WR_ADDR1_LSU_IN TOP.u_pipeline.WB_WR_ADDR2_LSU_IN TOP.u_pipeline.WB_WR_SIZE1_LSU_IN TOP.u_pipeline.LSU_OUT_WR_STALL_BAR TOP.u_pipeline.WB_WR_SIZE2_LSU_IN TOP.u_pipeline.ME2_V_LSU_IN TOP.u_pipeline.ME2_MEM_RD_LSU_IN TOP.u_pipeline.ME2_RD_ADDR1_V_LSU_IN TOP.u_pipeline.ME2_RD_ADDR2_V_LSU_IN TOP.u_pipeline.ME2_RD_ADDR1_LSU_IN TOP.u_pipeline.ME2_RD_ADDR2_LSU_IN TOP.u_pipeline.ME2_RD_SIZE1_LSU_IN TOP.u_pipeline.ME2_RD_SIZE2_LSU_IN TOP.u_pipeline.v_mem_wr_lsu_in TOP.u_pipeline.v_mem_rd_lsu_in TOP.u_pipeline.FE_EIP_IN TOP.u_pipeline.FE_JMP_FP TOP.u_pipeline.FE_TRAP_FP TOP.u_pipeline.FE_FP_MUX TOP.u_pipeline.FE_LD_EIP TOP.u_pipeline.FE_SEG_LIM_EXC TOP.u_pipeline.DE_PRE_PRES_IN TOP.u_pipeline.DE_SEG_OVR_IN TOP.u_pipeline.DE_OP_OVR_IN TOP.u_pipeline.DE_RE_PRE_IN TOP.u_pipeline.DE_MODRM_PRES_IN TOP.u_pipeline.DE_IMM_PRES_IN TOP.u_pipeline.DE_SIB_PRES_IN TOP.u_pipeline.DE_DISP_PRES_IN TOP.u_pipeline.DE_DISP_SIZE_IN TOP.u_pipeline.DE_OFFSET_PRES_IN TOP.u_pipeline.DE_OP_SIZE_IN TOP.u_pipeline.DE_IMM_SIZE_IN TOP.u_pipeline.DE_OFFSET_SIZE_IN TOP.u_pipeline.DE_PRE_SIZE_IN TOP.u_pipeline.DE_DISP_SEL_IN TOP.u_pipeline.DE_SEGID_IN TOP.u_pipeline.DE_MODRM_SEL_IN TOP.u_pipeline.DE_IMM_SEL_IN TOP.u_pipeline.DE_MODRM_IN TOP.u_pipeline.DE_SIB_IN TOP.u_pipeline.DE_OPCODE_IN TOP.u_pipeline.DE_CS_IN TOP.u_pipeline.DE_EIP_IN TOP.u_pipeline.DE_EIP_OUT TOP.u_pipeline.DE_EIP_OUT_BAR TOP.u_pipeline.IR_IN TOP.u_pipeline.DE_INSTR_LENGTH_UPDT_IN TOP.u_pipeline.DE_INSTR_LENGTH_UPDT_OUT TOP.u_pipeline.DE_INSTR_LENGTH_UPDT_OUT_T TOP.u_pipeline.DE_CONTROL_STORE_ADDRESS_IN TOP.u_pipeline.DE_CONTROL_STORE_ADDRESS TOP.u_pipeline.DE_CONTROL_STORE_ADDRESS_OUT TOP.u_pipeline.INT_EXIST_DE_IN TOP.u_pipeline.DEP_AND_MEM_STALLS TOP.u_pipeline.DEP_AND_MEM_STALLS_BAR TOP.u_pipeline.FETCH_STALL_OUT TOP.u_pipeline.FETCH_PAGE_FAULT_EXC_EXIST_OUT TOP.u_pipeline.DE_V_IN TOP.u_pipeline.LD_D2 TOP.u_pipeline.and0_ld_d2_out TOP.u_pipeline.AG_STALL_OUT_LD_D2_IN TOP.u_pipeline.D2_UOP_STALL_OUT TOP.u_pipeline.D2_UOP_STALL_OUT_BAR TOP.u_pipeline.D2_EXC_EN_V_OUT TOP.u_pipeline.AG_EXC_EN_V_OUT TOP.u_pipeline.AG2_EXC_EN_V_OUT TOP.u_pipeline.ME_EXC_EN_V_OUT TOP.u_pipeline.ME2_EXC_EN_V_OUT TOP.u_pipeline.EX_EXC_EN_V_OUT TOP.u_pipeline.D2_JMP_STALL_OUT TOP.u_pipeline.AG_JMP_STALL_OUT TOP.u_pipeline.AG2_JMP_STALL_OUT TOP.u_pipeline.ME_JMP_STALL_OUT TOP.u_pipeline.ME2_JMP_STALL_OUT TOP.u_pipeline.EX_JMP_STALL_OUT TOP.u_pipeline.nor0_de_v_exc_out TOP.u_pipeline.nor1_de_v_exc_out TOP.u_pipeline.nor2_de_v_exc_out TOP.u_pipeline.fetch_stall_out_bar TOP.u_pipeline.and0_de_v_out TOP.u_pipeline.wb_mispredict_taken_all_bar TOP.u_pipeline.nor3_de_v_exc_out TOP.u_pipeline.DE_V_OUT_T TOP.u_pipeline.DE_V_OUT_T_BAR TOP.u_pipeline.DE_OP_CS_OUT_T TOP.u_pipeline.DE_OP_CS_OUT_T_BAR TOP.u_pipeline.MOD_SIB_OUT TOP.u_pipeline.MOD_SIB_OUT_BAR TOP.u_pipeline.IR_OUT TOP.u_pipeline.IR_BAR_OUT TOP.u_pipeline.DE_PRE_SIZE_OUT TOP.u_pipeline.DE_OFFSET_SIZE_OUT TOP.u_pipeline.DE_IMM_SIZE_OUT TOP.u_pipeline.DE_MODRM_SEL_OUT TOP.u_pipeline.DE_SEGID_OUT TOP.u_pipeline.DE_DISP_SEL_OUT TOP.u_pipeline.DE_IMM_SEL_OUT TOP.u_pipeline.DE_SIB_PRES_OUT TOP.u_pipeline.DE_IMM_PRES_OUT TOP.u_pipeline.D2_V TOP.u_pipeline.DE_MODRM_PRES_OUT TOP.u_pipeline.DE_RE_PRE_OUT TOP.u_pipeline.DE_OP_OVR_OUT TOP.u_pipeline.DE_SEG_OVR_OUT TOP.u_pipeline.DE_PRE_PRES_OUT TOP.u_pipeline.DE_OP_SIZE_OUT TOP.u_pipeline.DE_OFFSET_PRES_OUT TOP.u_pipeline.DE_DISP_SIZE_OUT TOP.u_pipeline.DE_DISP_PRES_OUT TOP.u_pipeline.DE_SIB_OUT TOP.u_pipeline.DE_MODRM_OUT TOP.u_pipeline.DE_OPCODE_OUT TOP.u_pipeline.DE_CS_OUT TOP.u_pipeline.DE_INSTR_LENGTH_UPDATE_OUT TOP.u_pipeline.D2_EIP_OUT TOP.u_pipeline.D2_CS_OUT TOP.u_pipeline.D2_CONTROL_STORE_OUT TOP.u_pipeline.D2_OFFSET_OUT TOP.u_pipeline.D2_SR1_NEEDED_AG_OUT TOP.u_pipeline.D2_SEG1_NEEDED_AG_OUT TOP.u_pipeline.D2_MM1_NEEDED_AG_OUT TOP.u_pipeline.D2_MEM_RD_ME_OUT TOP.u_pipeline.D2_MEM_WR_ME_OUT }
gui_sg_addsignal -group "$_session_group_128" { TOP.u_pipeline.D2_ALUK_EX_OUT TOP.u_pipeline.D2_LD_GPR1_WB_OUT TOP.u_pipeline.D2_LD_MM_WB_OUT TOP.u_pipeline.D2_IMM32_OUT TOP.u_pipeline.D2_DISP32_OUT TOP.u_pipeline.D2_SIB_EN_AG TOP.u_pipeline.D2_DISP_EN_AG TOP.u_pipeline.D2_BASE_REG_EN_AG TOP.u_pipeline.D2_MUX_SEG_AG TOP.u_pipeline.D2_CMPXCHG_AG TOP.u_pipeline.D2_SIB_S_AG TOP.u_pipeline.D2_SR1_OUT TOP.u_pipeline.D2_SR2_OUT TOP.u_pipeline.D2_SR3_OUT TOP.u_pipeline.D2_SIB_I_OUT TOP.u_pipeline.D2_SEG1_OUT TOP.u_pipeline.D2_SEG2_OUT TOP.u_pipeline.D2_SR1_SIZE_AG_OUT TOP.u_pipeline.D2_SR2_SIZE_AG_OUT TOP.u_pipeline.D2_DR1_SIZE_WB_OUT TOP.u_pipeline.D2_DR2_SIZE_WB_OUT TOP.u_pipeline.D2_MEM_SIZE_WB_OUT TOP.u_pipeline.D2_PAGE_FAULT_EXC_EXIST_OUT TOP.u_pipeline.D2_NMI_INT_EN_OUT TOP.u_pipeline.D2_GEN_PROT_EXC_EN_OUT TOP.u_pipeline.D2_PAGE_FAULT_EXC_EN_OUT TOP.u_pipeline.D2_REPNE_WB_OUT TOP.u_pipeline.D2_PS_SAVE_INT_STATUS TOP.u_pipeline.D2_PS_PAGE_FAULT_EXC_EXIST TOP.u_pipeline.D2_PS_NMI_INT_EN TOP.u_pipeline.D2_PS_GEN_PROT_EXC_EN TOP.u_pipeline.D2_PS_PAGE_FAULT_EXC_EN TOP.u_pipeline.d2_ps_v_stage_in TOP.u_pipeline.d2_ps_page_fault_exc_exist_bar TOP.u_pipeline.AG_PS_EIP TOP.u_pipeline.AG_PS_CS TOP.u_pipeline.AG_PS_CS_NC TOP.u_pipeline.AG_PS_REPNE_WB TOP.u_pipeline.AG_PS_CONTROL_STORE TOP.u_pipeline.AG_PS_OFFSET TOP.u_pipeline.AG_PS_D2_SR1_NEEDED_AG TOP.u_pipeline.AG_PS_D2_SEG1_NEEDED_AG TOP.u_pipeline.AG_PS_D2_MM1_NEEDED_AG TOP.u_pipeline.AG_PS_D2_MEM_RD_ME TOP.u_pipeline.AG_PS_D2_MEM_WR_ME TOP.u_pipeline.AG_PS_D2_ALUK_EX TOP.u_pipeline.AG_PS_D2_LD_GPR1_WB TOP.u_pipeline.AG_PS_D2_LD_MM_WB TOP.u_pipeline.AG_PS_SR1 TOP.u_pipeline.AG_PS_SR2 TOP.u_pipeline.AG_PS_SR3 TOP.u_pipeline.AG_PS_SIB_I TOP.u_pipeline.AG_PS_SEG1 TOP.u_pipeline.AG_PS_SEG2 TOP.u_pipeline.AG_PS_D2_SR1_SIZE_AG TOP.u_pipeline.AG_PS_D2_SR2_SIZE_AG TOP.u_pipeline.AG_PS_D2_DR1_SIZE_WB TOP.u_pipeline.AG_PS_D2_DR2_SIZE_WB TOP.u_pipeline.AG_PS_D2_MEM_SIZE_WB TOP.u_pipeline.AG_PS_IMM32 TOP.u_pipeline.AG_PS_DISP32 TOP.u_pipeline.AG_PS_DE_SIB_EN_AG TOP.u_pipeline.AG_PS_DE_DISP_EN_AG TOP.u_pipeline.AG_PS_DE_BASE_REG_EN_AG TOP.u_pipeline.AG_PS_DE_MUX_SEG_AG TOP.u_pipeline.AG_PS_DE_CMPXCHG_AG TOP.u_pipeline.AG_PS_DE_SIB_S_AG TOP.u_pipeline.AG_PS_PAGE_FAULT_EXC_EXIST TOP.u_pipeline.AG_PS_NMI_INT_EN TOP.u_pipeline.AG_PS_GEN_PROT_EXC_EN TOP.u_pipeline.AG_PS_PAGE_FAULT_EXC_EN TOP.u_pipeline.AG_SR1_OUT TOP.u_pipeline.AG_SR2_OUT TOP.u_pipeline.AG_SR3_OUT TOP.u_pipeline.AG_SIB_I_OUT TOP.u_pipeline.AG_SEG1_OUT TOP.u_pipeline.AG_SEG2_OUT TOP.u_pipeline.AG_MM1_OUT TOP.u_pipeline.AG_MM2_OUT TOP.u_pipeline.AG_D2_SR1_SIZE_AG_OUT TOP.u_pipeline.AG_D2_SR2_SIZE_AG_OUT TOP.u_pipeline.AG_D2_SR3_SIZE_AG_OUT TOP.u_pipeline.AG_D2_SR4_SIZE_AG_OUT TOP.u_pipeline.AG_D2_DR1_SIZE_WB_OUT TOP.u_pipeline.AG_D2_DR2_SIZE_WB_OUT TOP.u_pipeline.AG_D2_MEM_SIZE_WB_OUT TOP.u_pipeline.AG_EIP_OUT TOP.u_pipeline.AG_NEIP_OUT TOP.u_pipeline.AG_NCS_OUT TOP.u_pipeline.AG_CONTROL_STORE_OUT TOP.u_pipeline.AG_REPNE_WB_OUT TOP.u_pipeline.AG_A_OUT TOP.u_pipeline.AG_B_OUT TOP.u_pipeline.AG_MM_A_OUT TOP.u_pipeline.AG_MM_B_OUT TOP.u_pipeline.AG_SP_XCHG_DATA_OUT TOP.u_pipeline.AG_ADD_BASE_DISP_OUT TOP.u_pipeline.AG_ADD_SIB_SEG1_OUT TOP.u_pipeline.AG_SIB_SI_DATA_OUT TOP.u_pipeline.AG_SEG1_DATA_OUT TOP.u_pipeline.AG_SEG2_DATA_OUT TOP.u_pipeline.AG_INTERRUPT_ADDR_OUT TOP.u_pipeline.AG_D2_ALUK_EX_OUT TOP.u_pipeline.AG_DRID1_OUT TOP.u_pipeline.AG_DRID2_OUT TOP.u_pipeline.AG_D2_MEM_RD_ME_OUT TOP.u_pipeline.AG_D2_MEM_WR_WB_OUT TOP.u_pipeline.AG_D2_LD_GPR1_WB_OUT TOP.u_pipeline.AG_D2_LD_MM_WB_OUT TOP.u_pipeline.AG_PAGE_FAULT_EXC_EXIST_OUT TOP.u_pipeline.D2_OUT1_AG_PS TOP.u_pipeline.D2_OUT2_AG_PS TOP.u_pipeline.AG_PS_IN1 TOP.u_pipeline.AG_PS_IN2 TOP.u_pipeline.D2_CS_OUT32 TOP.u_pipeline.D2_AG_V_OUT TOP.u_pipeline.LD_AG TOP.u_pipeline.AG2_PS_V_OUT_AG_IN TOP.u_pipeline.ME_PS_V_OUT_AG_IN TOP.u_pipeline.ME2_PS_V_OUT_AG_IN TOP.u_pipeline.EX_PS_V_OUT_AG_IN TOP.u_pipeline.AG_MM_SCOREBOARD_OUT TOP.u_pipeline.AG2_SEG_SCOREBOARD_OUT TOP.u_pipeline.ME2_SEG_SCOREBOARD_OUT TOP.u_pipeline.EX_SEG_SCOREBOARD_OUT TOP.u_pipeline.AG2_MM_SCOREBOARD_OUT }
gui_sg_addsignal -group "$_session_group_128" { TOP.u_pipeline.AG_PS_V TOP.u_pipeline.ME_MM_SCOREBOARD_OUT TOP.u_pipeline.ME2_MM_SCOREBOARD_OUT TOP.u_pipeline.EX_MM_SCOREBOARD_OUT TOP.u_pipeline.nor_ld_ag_out TOP.u_pipeline.AG_PS_OFFSET_OUT TOP.u_pipeline.ag_ps_page_fault_exc_exist_bar TOP.u_pipeline.AG_GPR_SCOREBOARD_OUT TOP.u_pipeline.ag_ps_v_stage_in TOP.u_pipeline.AG2_V_LD_DF_OUT TOP.u_pipeline.AG_SEG_SCOREBOARD_OUT TOP.u_pipeline.ME_V_LD_DF_OUT TOP.u_pipeline.AG2_GPR_SCOREBOARD_OUT TOP.u_pipeline.ME2_V_LD_DF_OUT TOP.u_pipeline.EX_V_LD_DF_OUT TOP.u_pipeline.ME_GPR_SCOREBOARD_OUT TOP.u_pipeline.AG2_PS_EIP TOP.u_pipeline.ME2_GPR_SCOREBOARD_OUT TOP.u_pipeline.AG2_PS_NEIP TOP.u_pipeline.EX_GPR_SCOREBOARD_OUT TOP.u_pipeline.AG2_PS_NCS_NC TOP.u_pipeline.AG2_PS_NCS TOP.u_pipeline.ME_SEG_SCOREBOARD_OUT TOP.u_pipeline.AG2_PS_CONTROL_STORE TOP.u_pipeline.AG2_PS_REPNE_WB TOP.u_pipeline.AG2_PS_A TOP.u_pipeline.AG2_PS_B TOP.u_pipeline.AG2_PS_MM_A TOP.u_pipeline.AG2_PS_MM_B TOP.u_pipeline.AG2_PS_SP_XCHG_DATA TOP.u_pipeline.AG2_PS_ADD_BASE_DISP TOP.u_pipeline.AG2_PS_ADD_SIB_SEG1 TOP.u_pipeline.AG2_PS_SIB_SI_DATA TOP.u_pipeline.AG2_PS_SEG1_DATA_NC TOP.u_pipeline.AG2_PS_SEG1_DATA TOP.u_pipeline.AG2_PS_SEG2_DATA_NC TOP.u_pipeline.AG2_PS_SEG2_DATA TOP.u_pipeline.AG2_PS_INTERRUPT_ADDR TOP.u_pipeline.AG2_PS_SEG1 TOP.u_pipeline.AG2_PS_D2_ALUK_EX TOP.u_pipeline.AG2_PS_DRID1 TOP.u_pipeline.AG2_PS_DRID2 TOP.u_pipeline.AG2_PS_D2_MEM_RD_ME TOP.u_pipeline.AG2_PS_D2_MEM_WR_WB TOP.u_pipeline.AG2_PS_D2_LD_GPR1_WB TOP.u_pipeline.AG2_PS_D2_LD_MM_WB TOP.u_pipeline.AG2_PS_D2_DR1_SIZE_WB TOP.u_pipeline.AG2_PS_D2_DR2_SIZE_WB TOP.u_pipeline.AG2_PS_D2_MEM_SIZE_WB TOP.u_pipeline.AG2_PS_PAGE_FAULT_EXC_EXIST TOP.u_pipeline.AG2_PS_EXC_EN_V TOP.u_pipeline.AG2_D2_DR1_SIZE_WB_OUT TOP.u_pipeline.AG2_D2_DR2_SIZE_WB_OUT TOP.u_pipeline.AG2_D2_MEM_SIZE_WB_OUT TOP.u_pipeline.AG_AG2_V_OUT TOP.u_pipeline.LD_AG2 TOP.u_pipeline.AG2_NEIP_OUT TOP.u_pipeline.AG2_NCS_OUT TOP.u_pipeline.AG2_CONTROL_STORE_OUT TOP.u_pipeline.AG2_REPNE_WB_OUT TOP.u_pipeline.AG2_A_OUT TOP.u_pipeline.AG2_B_OUT TOP.u_pipeline.AG2_MM_A_OUT TOP.u_pipeline.AG2_MM_B_OUT TOP.u_pipeline.AG2_SP_XCHG_DATA_OUT TOP.u_pipeline.AG2_MEM_RD_ADDR_OUT TOP.u_pipeline.AG2_MEM_WR_ADDR_OUT TOP.u_pipeline.AG2_D2_ALUK_EX_OUT TOP.u_pipeline.AG2_DRID1_OUT TOP.u_pipeline.AG2_DRID2_OUT TOP.u_pipeline.AG2_D2_MEM_RD_ME_OUT TOP.u_pipeline.AG2_D2_MEM_WR_WB_OUT TOP.u_pipeline.AG2_D2_LD_GPR1_WB_OUT TOP.u_pipeline.AG2_D2_LD_MM_WB_OUT TOP.u_pipeline.AG2_PS_V TOP.u_pipeline.AG2_SEG_LIMIT_EXC_EXIST_OUT TOP.u_pipeline.AG2_PAGE_FAULT_EXC_EXIST_OUT TOP.u_pipeline.ag_dep_stall_out_bar TOP.u_pipeline.and_flush_ag2_v_out TOP.u_pipeline.ME_STALL_OUT_LD_AG2_IN TOP.u_pipeline.ag2_ps_save_sb TOP.u_pipeline.AG2_PS_SCOREBOARDS TOP.u_pipeline.AG_OUT1_AG2_PS TOP.u_pipeline.AG2_PS_IN1 TOP.u_pipeline.EFLAGS_DF TOP.u_pipeline.ag2_ps_page_fault_exc_exist_bar TOP.u_pipeline.ME_PS_NEIP TOP.u_pipeline.ME_PS_NEIP_NOT_TAKEN TOP.u_pipeline.ME_PS_NCS TOP.u_pipeline.ME_PS_NCS_NC TOP.u_pipeline.ME_PS_CONTROL_STORE TOP.u_pipeline.ME_PS_A TOP.u_pipeline.ME_PS_B TOP.u_pipeline.ME_PS_MM_A TOP.u_pipeline.ME_PS_MM_B TOP.u_pipeline.ME_PS_SP_XCHG_DATA TOP.u_pipeline.ME_PS_MEM_RD_ADDR TOP.u_pipeline.ME_PS_MEM_WR_ADDR TOP.u_pipeline.ME_PS_D2_DR1_SIZE_WB TOP.u_pipeline.ME_PS_D2_DR2_SIZE_WB TOP.u_pipeline.ME_PS_D2_MEM_SIZE_WB TOP.u_pipeline.ME_PS_D2_REPNE_WB TOP.u_pipeline.ME_PS_D2_ALUK_EX TOP.u_pipeline.ME_PS_DRID1 TOP.u_pipeline.ME_PS_DRID2 TOP.u_pipeline.ME_PS_D2_MEM_RD_ME TOP.u_pipeline.ag2_ps_v_stage_in TOP.u_pipeline.ME_PS_D2_MEM_WR_WB TOP.u_pipeline.ME_PS_V TOP.u_pipeline.ME_PS_D2_LD_GPR1_WB TOP.u_pipeline.ME_PS_D2_LD_MM_WB TOP.u_pipeline.ME_PS_GPROT_EXC_EXIST TOP.u_pipeline.ME_PS_PAGE_FAULT_EXC_EXIST TOP.u_pipeline.ME_PS_EXC_EN_V TOP.u_pipeline.ME_MEM_WR_ADDR_OUT TOP.u_pipeline.ME_D2_MEM_SIZE_WB_OUT TOP.u_pipeline.ME_D2_MEM_WR_WB_OUT TOP.u_pipeline.ME_RD_ADDR1_V_OUT TOP.u_pipeline.ME_RD_ADDR2_V_OUT TOP.u_pipeline.ME_WR_ADDR1_V_OUT TOP.u_pipeline.ME_WR_ADDR2_V_OUT TOP.u_pipeline.ME_RA_RD_ADDR1_OUT TOP.u_pipeline.ME_RA_RD_ADDR2_OUT TOP.u_pipeline.ME_RA_WR_ADDR1_OUT }
gui_sg_addsignal -group "$_session_group_128" { TOP.u_pipeline.ME_RA_WR_ADDR2_OUT TOP.u_pipeline.ME_RA_RD_SIZE1_OUT TOP.u_pipeline.ME_RA_RD_SIZE2_OUT TOP.u_pipeline.ME_RA_WR_SIZE1_OUT TOP.u_pipeline.ME_RA_WR_SIZE2_OUT TOP.u_pipeline.ME_PAGE_FAULT_EXC_OUT TOP.u_pipeline.ME_GPROT_EXC_OUT TOP.u_pipeline.AG2_OUT1_ME_PS TOP.u_pipeline.ME_PS_IN1 TOP.u_pipeline.LD_ME TOP.u_pipeline.AG2_ME_V_OUT TOP.u_pipeline.nor_ld_me_out TOP.u_pipeline.me_ps_save_sb TOP.u_pipeline.ME_PS_SCOREBOARDS TOP.u_pipeline.nor_me_exc_exist_out TOP.u_pipeline.me_ps_v_stage_in TOP.u_pipeline.ME2_V_ME_IN TOP.u_pipeline.ME2_WR_ADDR1_V_ME_IN TOP.u_pipeline.ME2_WR_ADDR2_V_ME_IN TOP.u_pipeline.EX_V_ME_IN TOP.u_pipeline.EX_WR_ADDR1_V_ME_IN TOP.u_pipeline.EX_WR_ADDR2_V_ME_IN TOP.u_pipeline.ME2_WR_ADDR1_ME_IN TOP.u_pipeline.ME2_WR_ADDR2_ME_IN TOP.u_pipeline.EX_WR_ADDR1_ME_IN TOP.u_pipeline.EX_WR_ADDR2_ME_IN TOP.u_pipeline.ME2_WR_SIZE1_ME_IN TOP.u_pipeline.ME2_WR_SIZE2_ME_IN TOP.u_pipeline.EX_WR_SIZE1_ME_IN TOP.u_pipeline.EX_WR_SIZE2_ME_IN TOP.u_pipeline.ME_PAGE_FAULT_EXC_EXIST_OUT TOP.u_pipeline.ME_GPROT_EXC_EXIST_OUT TOP.u_pipeline.ME2_PS_NEIP TOP.u_pipeline.ME2_PS_NEIP_NOT_TAKEN TOP.u_pipeline.ME2_PS_NCS TOP.u_pipeline.ME2_PS_NCS_NC TOP.u_pipeline.ME2_PS_CONTROL_STORE TOP.u_pipeline.ME2_PS_A TOP.u_pipeline.ME2_PS_B TOP.u_pipeline.ME2_PS_MM_A TOP.u_pipeline.ME2_PS_MM_B TOP.u_pipeline.ME2_PS_SP_XCHG_DATA TOP.u_pipeline.ME2_PS_MEM_RD_ADDR TOP.u_pipeline.ME2_PS_MEM_WR_ADDR TOP.u_pipeline.ME2_PS_D2_DR1_SIZE_WB TOP.u_pipeline.ME2_PS_D2_DR2_SIZE_WB TOP.u_pipeline.ME2_PS_D2_MEM_SIZE_WB TOP.u_pipeline.ME2_PS_D2_ALUK_EX TOP.u_pipeline.ME2_PS_DRID1 TOP.u_pipeline.ME2_PS_DRID2 TOP.u_pipeline.ME2_PS_D2_MEM_RD_ME TOP.u_pipeline.ME2_PS_D2_MEM_WR_WB TOP.u_pipeline.ME2_PS_D2_LD_GPR1_WB TOP.u_pipeline.ME2_PS_D2_LD_MM_WB TOP.u_pipeline.ME2_PS_V TOP.u_pipeline.DCACHE_DATA TOP.u_pipeline.DCACHE_READY TOP.u_pipeline.ME2_DCACHE_EN TOP.u_pipeline.ME2_NEIP_OUT TOP.u_pipeline.ME2_NCS_OUT TOP.u_pipeline.ME2_CONTROL_STORE_OUT TOP.u_pipeline.ME2_A_OUT TOP.u_pipeline.ME2_B_OUT TOP.u_pipeline.ME2_MM_A_OUT TOP.u_pipeline.ME2_MM_B_OUT TOP.u_pipeline.ME2_SP_XCHG_DATA_OUT TOP.u_pipeline.ME2_MEM_RD_ADDR_OUT TOP.u_pipeline.ME2_MEM_WR_ADDR_OUT TOP.u_pipeline.ME2_D2_DR1_SIZE_WB_OUT TOP.u_pipeline.ME2_D2_DR2_SIZE_WB_OUT TOP.u_pipeline.ME2_D2_MEM_SIZE_WB_OUT TOP.u_pipeline.ME2_PS_D2_REPNE_WB TOP.u_pipeline.ME2_D2_ALUK_EX_OUT TOP.u_pipeline.ME2_DRID1_OUT TOP.u_pipeline.ME2_DRID2_OUT TOP.u_pipeline.ME2_D2_MEM_WR_WB_OUT TOP.u_pipeline.ME2_D2_LD_GPR1_WB_OUT TOP.u_pipeline.ME2_D2_LD_MM_WB_OUT TOP.u_pipeline.ME_OUT1_ME2_PS TOP.u_pipeline.ME2_PS_IN1 TOP.u_pipeline.LD_ME2 TOP.u_pipeline.ME_ME2_V_OUT TOP.u_pipeline.nor_me2_v_out TOP.u_pipeline.me_mem_dep_stall_out_bar TOP.u_pipeline.nor_ld_me2_out TOP.u_pipeline.me2_ps_save_sb TOP.u_pipeline.ME2_PS_SCOREBOARDS TOP.u_pipeline.me2_ps_save_rd_ra TOP.u_pipeline.me2_ps_save_wr_ra TOP.u_pipeline.ME2_PS_RD_RA TOP.u_pipeline.ME2_PS_WR_RA TOP.u_pipeline.ME2_PS_RA_RD_ADDR1 TOP.u_pipeline.ME2_PS_RA_RD_ADDR2 TOP.u_pipeline.ME2_PS_RA_WR_ADDR1 TOP.u_pipeline.ME2_PS_RA_WR_ADDR2 TOP.u_pipeline.me2_ps_save_mem TOP.u_pipeline.ME2_PS_SAVE_MEM TOP.u_pipeline.ME2_PS_RD_ADDR1_V TOP.u_pipeline.ME2_PS_RD_ADDR2_V TOP.u_pipeline.ME2_PS_WR_ADDR1_V TOP.u_pipeline.ME2_PS_WR_ADDR2_V TOP.u_pipeline.ME2_PS_RA_RD_SIZE1 TOP.u_pipeline.ME2_PS_RA_RD_SIZE2 TOP.u_pipeline.ME2_PS_RA_WR_SIZE1 TOP.u_pipeline.ME2_PS_RA_WR_SIZE2 TOP.u_pipeline.ME2_PS_PAGE_FAULT_EXC_EXIST TOP.u_pipeline.ME2_PS_GPROT_EXC_EXIST TOP.u_pipeline.ME2_PS_EXC_EN_V TOP.u_pipeline.nor_me2_exc_exist_out TOP.u_pipeline.me2_ps_v_stage_in TOP.u_pipeline.LD_EX TOP.u_pipeline.EX_V_next TOP.u_pipeline.EX_V_out TOP.u_pipeline.nor_ex_v_out TOP.u_pipeline.ex_ps_save_sb TOP.u_pipeline.EX_PS_SCOREBOARDS TOP.u_pipeline.ex_ps_save_wr_ra TOP.u_pipeline.EX_PS_WR_RA TOP.u_pipeline.EX_PS_RA_WR_ADDR1 TOP.u_pipeline.EX_PS_RA_WR_ADDR2 TOP.u_pipeline.ex_ps_save_mem TOP.u_pipeline.EX_PS_SAVE_MEM TOP.u_pipeline.EX_PS_WR_ADDR1_V TOP.u_pipeline.EX_PS_WR_ADDR2_V TOP.u_pipeline.EX_PS_RA_WR_SIZE1 TOP.u_pipeline.EX_PS_RA_WR_SIZE2 }
gui_sg_addsignal -group "$_session_group_128" { TOP.u_pipeline.EX_PS_PAGE_FAULT_EXC_EXIST TOP.u_pipeline.EX_PS_GPROT_EXC_EXIST TOP.u_pipeline.EX_PS_EXC_EN_V TOP.u_pipeline.EX_PS_REPNE_WB TOP.u_pipeline.nor_ex_exc_exist_out TOP.u_pipeline.ex_ps_v_stage_in TOP.u_pipeline.EX_NEIP_next TOP.u_pipeline.EX_V TOP.u_pipeline.EX_NEIP TOP.u_pipeline.EX_NEIP_NOT_TAKEN TOP.u_pipeline.EX_NCS_next TOP.u_pipeline.EX_NCS_out TOP.u_pipeline.EX_NCS TOP.u_pipeline.EX_CONTROL_STORE_next TOP.u_pipeline.EX_CONTROL_STORE TOP.u_pipeline.EX_d2_datasize_all_next TOP.u_pipeline.EX_d2_datasize_all_out TOP.u_pipeline.EX_d2_datasize_all TOP.u_pipeline.EX_d2_aluk_ex_next TOP.u_pipeline.EX_d2_aluk_ex_out TOP.u_pipeline.EX_d2_aluk_ex TOP.u_pipeline.EX_d2_ld_gpr1_ex_next TOP.u_pipeline.EX_d2_ld_gpr1_ex_out TOP.u_pipeline.EX_d2_ld_gpr1_ex TOP.u_pipeline.EX_d2_dcache_write_ex_next TOP.u_pipeline.EX_d2_dcache_write_ex_out TOP.u_pipeline.EX_d2_dcache_write_ex TOP.u_pipeline.EX_d2_repne_wb_next TOP.u_pipeline.EX_d2_repne_wb_out TOP.u_pipeline.EX_d2_repne_wb TOP.u_pipeline.EX_A_next TOP.u_pipeline.EX_B_next TOP.u_pipeline.EX_C_next TOP.u_pipeline.EX_A TOP.u_pipeline.EX_B TOP.u_pipeline.EX_C TOP.u_pipeline.EX_MM_A_next TOP.u_pipeline.EX_MM_B_next TOP.u_pipeline.EX_MM_A TOP.u_pipeline.EX_MM_B TOP.u_pipeline.EX_DR1_next TOP.u_pipeline.EX_DR2_next TOP.u_pipeline.EX_DR1_out TOP.u_pipeline.EX_DR2_out TOP.u_pipeline.EX_DR1 TOP.u_pipeline.EX_DR2 TOP.u_pipeline.EX_ADDRESS_next TOP.u_pipeline.EX_ADDRESS TOP.u_pipeline.WB_V_next TOP.u_pipeline.WB_NEIP_next TOP.u_pipeline.WB_NCS_next TOP.u_pipeline.WB_CONTROL_STORE_next TOP.u_pipeline.WB_de_datasize_all_next TOP.u_pipeline.WB_ex_ld_gpr1_wb_next TOP.u_pipeline.WB_ex_ld_gpr2_wb_next TOP.u_pipeline.WB_ex_dcache_write_wb_next TOP.u_pipeline.WB_de_repne_wb_next TOP.u_pipeline.WB_RESULT_A_next TOP.u_pipeline.WB_RESULT_B_next TOP.u_pipeline.WB_RESULT_C_next TOP.u_pipeline.WB_FLAGS_next TOP.u_pipeline.WB_RESULT_MM_next TOP.u_pipeline.WB_DR1_next TOP.u_pipeline.WB_DR2_next TOP.u_pipeline.WB_DR3_next TOP.u_pipeline.WB_ADDRESS_next TOP.u_pipeline.LD_WB TOP.u_pipeline.or_wb_exc_out TOP.u_pipeline.and_wb_exc_v_out TOP.u_pipeline.nor_wb_v_out TOP.u_pipeline.EX_OUT_WB_V_IN TOP.u_pipeline.WB_PS_PAGE_FAULT_EXC_EXIST TOP.u_pipeline.WB_V TOP.u_pipeline.WB_PS_GPROT_EXC_EXIST TOP.u_pipeline.WB_PS_EXC_EN_V TOP.u_pipeline.WB_V_out TOP.u_pipeline.wb_ps_save_wr_ra TOP.u_pipeline.WB_PS_WR_RA TOP.u_pipeline.WB_PS_RA_WR_ADDR1 TOP.u_pipeline.WB_PS_RA_WR_ADDR2 TOP.u_pipeline.wb_ps_save_mem TOP.u_pipeline.WB_PS_SAVE_MEM TOP.u_pipeline.WB_PS_WR_ADDR1_V TOP.u_pipeline.WB_PS_WR_ADDR2_V TOP.u_pipeline.WB_PS_RA_WR_SIZE1 TOP.u_pipeline.WB_PS_RA_WR_SIZE2 TOP.u_pipeline.nor_wb_exc_exist_out TOP.u_pipeline.wb_ps_v_stage_in TOP.u_pipeline.WB_NEIP TOP.u_pipeline.WB_NEIP_NOT_TAKEN TOP.u_pipeline.WB_NCS_out TOP.u_pipeline.WB_NCS TOP.u_pipeline.WB_CONTROL_STORE TOP.u_pipeline.WB_de_datasize_all_out TOP.u_pipeline.WB_de_datasize_all TOP.u_pipeline.WB_ex_ld_gpr1_wb_out TOP.u_pipeline.WB_ex_ld_gpr1_wb TOP.u_pipeline.WB_ex_ld_gpr2_wb_out TOP.u_pipeline.WB_ex_ld_gpr2_wb TOP.u_pipeline.WB_ex_dcache_write_wb_out TOP.u_pipeline.WB_ex_dcache_write_wb TOP.u_pipeline.WB_de_repne_wb_out TOP.u_pipeline.WB_de_repne_wb TOP.u_pipeline.WB_RESULT_A TOP.u_pipeline.WB_RESULT_B TOP.u_pipeline.WB_RESULT_C TOP.u_pipeline.WB_FLAGS TOP.u_pipeline.WB_RESULT_MM TOP.u_pipeline.WB_DR1_out TOP.u_pipeline.WB_DR2_out TOP.u_pipeline.WB_DR1 TOP.u_pipeline.WB_DR2 TOP.u_pipeline.WB_ADDRESS TOP.u_pipeline.CLK TOP.u_pipeline.ME_MEM_DEP_STALL_OUT TOP.u_pipeline.SIB_I_DATA TOP.u_pipeline.SR1_DATA TOP.u_pipeline.SR2_DATA TOP.u_pipeline.SR3_DATA TOP.u_pipeline.WRSEGID }

set _session_group_129 u_reg_dependency_check
gui_sg_create "$_session_group_129"
set u_reg_dependency_check "$_session_group_129"

gui_sg_addsignal -group "$_session_group_129" { TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.STAGE_V TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SR1_ID TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SR2_ID TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SR3_ID TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SIB_I_ID TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SEG1_ID TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SEG2_ID TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SR1_SIZE TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SR2_SIZE TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SR3_SIZE TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SIB_I_SIZE TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SR1_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SR2_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SR3_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SIB_I_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SEG1_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.SEG2_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.MM1_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.MM2_NEEDED TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.AG2_V TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.AG2_GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.AG2_SEG_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.AG2_MM_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.ME_V TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.ME_GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.ME_SEG_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.ME_MM_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.ME2_V TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.ME2_GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.ME2_SEG_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.ME2_MM_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.EX_V TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.EX_GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.EX_SEG_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.EX_MM_SCOREBOARD TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.DEP_STALL TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and3_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and6_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and9_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and2_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and4_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and5_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and8_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and11_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.or0_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.or1_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.or2_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.or3_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.or4_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.or5_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and7_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.and10_out TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.gpr_scoreboard TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.seg_scoreboard TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.mm_scoreboard TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.seg1_stall TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.seg2_stall TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.mm1_stall TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.mm2_stall TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.sr1_stall TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.sr2_stall TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.sr3_stall }
gui_sg_addsignal -group "$_session_group_129" { TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.sr4_stall TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.or6_out }

set _session_group_130 $_session_group_129|
append _session_group_130 u_agen_stage1
gui_sg_create "$_session_group_130"
set u_reg_dependency_check|u_agen_stage1 "$_session_group_130"

gui_sg_addsignal -group "$_session_group_130" { TOP.u_pipeline.u_agen_stage1.D2_REPNE_WB TOP.u_pipeline.u_agen_stage1.cs_repne_steady_state_bar TOP.u_pipeline.u_agen_stage1.dep_df_stall TOP.u_pipeline.u_agen_stage1.ME2_MM_SCOREBOARD TOP.u_pipeline.u_agen_stage1.reg_dep_stall_out TOP.u_pipeline.u_agen_stage1.D2_MM1_NEEDED_AG TOP.u_pipeline.u_agen_stage1.ME_MM_SCOREBOARD TOP.u_pipeline.u_agen_stage1.V TOP.u_pipeline.u_agen_stage1.or_v_ld_df_out TOP.u_pipeline.u_agen_stage1.AG2_SEG_SCOREBOARD TOP.u_pipeline.u_agen_stage1.CS_IS_CMPXCHG_EX TOP.u_pipeline.u_agen_stage1.CLK TOP.u_pipeline.u_agen_stage1.RST TOP.u_pipeline.u_agen_stage1.SET TOP.u_pipeline.u_agen_stage1.EIP TOP.u_pipeline.u_agen_stage1.CS TOP.u_pipeline.u_agen_stage1.CONTROL_STORE TOP.u_pipeline.u_agen_stage1.OFFSET TOP.u_pipeline.u_agen_stage1.D2_SR1_NEEDED_AG TOP.u_pipeline.u_agen_stage1.D2_SEG1_NEEDED_AG TOP.u_pipeline.u_agen_stage1.D2_MEM_RD_ME TOP.u_pipeline.u_agen_stage1.D2_MEM_WR_ME TOP.u_pipeline.u_agen_stage1.D2_ALUK_EX TOP.u_pipeline.u_agen_stage1.D2_LD_GPR1_WB TOP.u_pipeline.u_agen_stage1.D2_LD_MM_WB TOP.u_pipeline.u_agen_stage1.SR1 TOP.u_pipeline.u_agen_stage1.SR2 TOP.u_pipeline.u_agen_stage1.SR3 TOP.u_pipeline.u_agen_stage1.SIB_I TOP.u_pipeline.u_agen_stage1.SEG1 TOP.u_pipeline.u_agen_stage1.SEG2 TOP.u_pipeline.u_agen_stage1.D2_SR1_SIZE_AG TOP.u_pipeline.u_agen_stage1.D2_SR2_SIZE_AG TOP.u_pipeline.u_agen_stage1.D2_DR1_SIZE_WB TOP.u_pipeline.u_agen_stage1.D2_DR2_SIZE_WB TOP.u_pipeline.u_agen_stage1.D2_MEM_SIZE_WB TOP.u_pipeline.u_agen_stage1.IMM32 TOP.u_pipeline.u_agen_stage1.DISP32 TOP.u_pipeline.u_agen_stage1.DE_SIB_EN_AG TOP.u_pipeline.u_agen_stage1.DE_DISP_EN_AG TOP.u_pipeline.u_agen_stage1.DE_BASE_REG_EN_AG TOP.u_pipeline.u_agen_stage1.DE_MUX_SEG_AG TOP.u_pipeline.u_agen_stage1.DE_CMPXCHG_AG TOP.u_pipeline.u_agen_stage1.DE_SIB_S_AG TOP.u_pipeline.u_agen_stage1.SR1_DATA TOP.u_pipeline.u_agen_stage1.SR2_DATA TOP.u_pipeline.u_agen_stage1.SR3_DATA TOP.u_pipeline.u_agen_stage1.SIB_I_DATA TOP.u_pipeline.u_agen_stage1.SEG1_DATA TOP.u_pipeline.u_agen_stage1.SEG2_DATA TOP.u_pipeline.u_agen_stage1.MM1_DATA TOP.u_pipeline.u_agen_stage1.MM2_DATA TOP.u_pipeline.u_agen_stage1.NMI_INT_EN TOP.u_pipeline.u_agen_stage1.GEN_PROT_EXC_EN TOP.u_pipeline.u_agen_stage1.PAGE_FAULT_EXC_EN TOP.u_pipeline.u_agen_stage1.PAGE_FAULT_EXC_EXIST TOP.u_pipeline.u_agen_stage1.AG2_V TOP.u_pipeline.u_agen_stage1.AG2_GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.AG2_MM_SCOREBOARD TOP.u_pipeline.u_agen_stage1.ME_V TOP.u_pipeline.u_agen_stage1.ME_GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.ME_SEG_SCOREBOARD TOP.u_pipeline.u_agen_stage1.ME2_V TOP.u_pipeline.u_agen_stage1.ME2_GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.ME2_SEG_SCOREBOARD TOP.u_pipeline.u_agen_stage1.EX_V TOP.u_pipeline.u_agen_stage1.EX_GPR_SCOREBOARD TOP.u_pipeline.u_agen_stage1.EX_SEG_SCOREBOARD TOP.u_pipeline.u_agen_stage1.EX_MM_SCOREBOARD TOP.u_pipeline.u_agen_stage1.AG2_V_LD_DF TOP.u_pipeline.u_agen_stage1.ME_V_LD_DF TOP.u_pipeline.u_agen_stage1.ME2_V_LD_DF TOP.u_pipeline.u_agen_stage1.EX_V_LD_DF TOP.u_pipeline.u_agen_stage1.SR1_OUT TOP.u_pipeline.u_agen_stage1.SR2_OUT TOP.u_pipeline.u_agen_stage1.SR3_OUT TOP.u_pipeline.u_agen_stage1.SIB_I_OUT TOP.u_pipeline.u_agen_stage1.SEG1_OUT TOP.u_pipeline.u_agen_stage1.SEG2_OUT TOP.u_pipeline.u_agen_stage1.MM1_OUT TOP.u_pipeline.u_agen_stage1.MM2_OUT TOP.u_pipeline.u_agen_stage1.D2_SR1_SIZE_AG_OUT TOP.u_pipeline.u_agen_stage1.D2_SR2_SIZE_AG_OUT TOP.u_pipeline.u_agen_stage1.D2_SR3_SIZE_AG_OUT TOP.u_pipeline.u_agen_stage1.D2_SR4_SIZE_AG_OUT TOP.u_pipeline.u_agen_stage1.D2_DR1_SIZE_WB_OUT TOP.u_pipeline.u_agen_stage1.D2_DR2_SIZE_WB_OUT TOP.u_pipeline.u_agen_stage1.D2_MEM_SIZE_WB_OUT TOP.u_pipeline.u_agen_stage1.EIP_OUT TOP.u_pipeline.u_agen_stage1.NEIP_OUT TOP.u_pipeline.u_agen_stage1.NCS_OUT TOP.u_pipeline.u_agen_stage1.CONTROL_STORE_OUT TOP.u_pipeline.u_agen_stage1.A_OUT TOP.u_pipeline.u_agen_stage1.B_OUT TOP.u_pipeline.u_agen_stage1.MM_A_OUT TOP.u_pipeline.u_agen_stage1.MM_B_OUT TOP.u_pipeline.u_agen_stage1.SP_XCHG_DATA_OUT TOP.u_pipeline.u_agen_stage1.ADD_BASE_DISP_OUT }
gui_sg_addsignal -group "$_session_group_130" { TOP.u_pipeline.u_agen_stage1.ADD_SIB_SEG1_OUT TOP.u_pipeline.u_agen_stage1.SIB_SI_DATA_OUT TOP.u_pipeline.u_agen_stage1.SEG1_DATA_OUT TOP.u_pipeline.u_agen_stage1.SEG2_DATA_OUT TOP.u_pipeline.u_agen_stage1.INTERRUPT_ADDR_OUT TOP.u_pipeline.u_agen_stage1.D2_ALUK_EX_OUT TOP.u_pipeline.u_agen_stage1.DRID1_OUT TOP.u_pipeline.u_agen_stage1.DRID2_OUT TOP.u_pipeline.u_agen_stage1.D2_MEM_RD_ME_OUT TOP.u_pipeline.u_agen_stage1.D2_MEM_WR_WB_OUT TOP.u_pipeline.u_agen_stage1.D2_LD_GPR1_WB_OUT TOP.u_pipeline.u_agen_stage1.D2_LD_MM_WB_OUT TOP.u_pipeline.u_agen_stage1.GPR_SCOREBOARD_OUT TOP.u_pipeline.u_agen_stage1.SEG_SCOREBOARD_OUT TOP.u_pipeline.u_agen_stage1.MM_SCOREBOARD_OUT TOP.u_pipeline.u_agen_stage1.DEP_STALL_OUT TOP.u_pipeline.u_agen_stage1.PAGE_FAULT_EXC_EXIST_OUT TOP.u_pipeline.u_agen_stage1.AG_REPNE_WB_OUT TOP.u_pipeline.u_agen_stage1.EXC_EN_V TOP.u_pipeline.u_agen_stage1.AG_JMP_STALL_OUT TOP.u_pipeline.u_agen_stage1.CS_UOP_STALL_DE TOP.u_pipeline.u_agen_stage1.CS_MUX_OP_SIZE_D2 TOP.u_pipeline.u_agen_stage1.CS_OP_SIZE_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_SR1_SIZE_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_SR2_SIZE_D2 TOP.u_pipeline.u_agen_stage1.CS_SR2_SIZE_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_DR1_SIZE_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_DR2_SIZE_D2 TOP.u_pipeline.u_agen_stage1.CS_PUSHPOP_SIZE_D2 TOP.u_pipeline.u_agen_stage1.CS_IS_FAR_CALL_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_MEM_RD_DE TOP.u_pipeline.u_agen_stage1.CS_MEM_RD_DE TOP.u_pipeline.u_agen_stage1.CS_JMP_STALL_DE TOP.u_pipeline.u_agen_stage1.CS_MUX_SR1_D2 TOP.u_pipeline.u_agen_stage1.CS_SR1_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_SR2_D2 TOP.u_pipeline.u_agen_stage1.CS_SR2_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_SEG1_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_SEG2_D2 TOP.u_pipeline.u_agen_stage1.CS_SR1_NEEDED_AG TOP.u_pipeline.u_agen_stage1.CS_SR2_NEEDED_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_SEG1_NEEDED_AG TOP.u_pipeline.u_agen_stage1.CS_SEG1_NEEDED_AG TOP.u_pipeline.u_agen_stage1.CS_SEG2_NEEDED_AG TOP.u_pipeline.u_agen_stage1.CS_MM1_NEEDED_AG TOP.u_pipeline.u_agen_stage1.CS_MM2_NEEDED_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_A_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_B_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_DRID1_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_EIP_JMP_REL_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_NEXT_EIP_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_NEXT_CSEG_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_SP_ADD_SIZE_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_TEMP_SP_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_SP_PUSH_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_MEM_RD_ADDR_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_MEM_WR_ADDR_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_IMM1_AG TOP.u_pipeline.u_agen_stage1.CS_MUX_B_ME TOP.u_pipeline.u_agen_stage1.CS_MUX_IMM_ADD_ME TOP.u_pipeline.u_agen_stage1.CS_IS_NEAR_RET_M2 TOP.u_pipeline.u_agen_stage1.CS_IS_FAR_RET_M2 TOP.u_pipeline.u_agen_stage1.CS_MUX_NEXT_EIP_M2 TOP.u_pipeline.u_agen_stage1.CS_MUX_NEXT_CSEG_M2 TOP.u_pipeline.u_agen_stage1.CS_IS_CMPS_FIRST_UOP_ALL TOP.u_pipeline.u_agen_stage1.CS_IS_CMPS_SECOND_UOP_ALL TOP.u_pipeline.u_agen_stage1.CS_REPNE_STEADY_STATE TOP.u_pipeline.u_agen_stage1.CS_LD_GPR1_D2 TOP.u_pipeline.u_agen_stage1.CS_DR1_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_DR1_D2 TOP.u_pipeline.u_agen_stage1.CS_LD_GPR2_EX TOP.u_pipeline.u_agen_stage1.CS_ALU_TO_B_EX TOP.u_pipeline.u_agen_stage1.CS_DR2_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_DR2_D2 TOP.u_pipeline.u_agen_stage1.CS_DCACHE_WRITE_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_MEM_WR_DE TOP.u_pipeline.u_agen_stage1.CS_LD_GPR3_WB TOP.u_pipeline.u_agen_stage1.CS_DR3_WB TOP.u_pipeline.u_agen_stage1.CS_ALUK_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_ALUK_D2 TOP.u_pipeline.u_agen_stage1.CS_IS_ALU32_EX TOP.u_pipeline.u_agen_stage1.CS_IS_ALU32_FLAGS_EX TOP.u_pipeline.u_agen_stage1.CS_IS_XCHG_EX TOP.u_pipeline.u_agen_stage1.CS_PASS_A_EX TOP.u_pipeline.u_agen_stage1.CS_POP_SIZE_D2 TOP.u_pipeline.u_agen_stage1.CS_MUX_SP_POP_EX TOP.u_pipeline.u_agen_stage1.CS_SAVE_NEIP_WB TOP.u_pipeline.u_agen_stage1.CS_SAVE_NCS_WB TOP.u_pipeline.u_agen_stage1.CS_PUSH_FLAGS_WB }
gui_sg_addsignal -group "$_session_group_130" { TOP.u_pipeline.u_agen_stage1.CS_POP_FLAGS_WB TOP.u_pipeline.u_agen_stage1.CS_USE_TEMP_NEIP_WB TOP.u_pipeline.u_agen_stage1.CS_USE_TEMP_NCS_WB TOP.u_pipeline.u_agen_stage1.CS_IS_JNBE_WB TOP.u_pipeline.u_agen_stage1.CS_IS_JNE_WB TOP.u_pipeline.u_agen_stage1.CS_LD_EIP_WB TOP.u_pipeline.u_agen_stage1.CS_LD_CS_WB TOP.u_pipeline.u_agen_stage1.CS_IS_CMOVC_WB TOP.u_pipeline.u_agen_stage1.CS_LD_SEG_WB TOP.u_pipeline.u_agen_stage1.CS_LD_MM_WB TOP.u_pipeline.u_agen_stage1.CS_MM_MEM_WB TOP.u_pipeline.u_agen_stage1.CS_LD_FLAGS_WB TOP.u_pipeline.u_agen_stage1.CS_IS_HALT_WB TOP.u_pipeline.u_agen_stage1.CS_FLAGS_AFFECTED_WB TOP.u_pipeline.u_agen_stage1.CS_MUX_MICROSEQUENCER_DE TOP.u_pipeline.u_agen_stage1.CS_NEXT_MICRO_ADDRESS_DE TOP.u_pipeline.u_agen_stage1.PLACEHOLDER TOP.u_pipeline.u_agen_stage1.mux_rel_out TOP.u_pipeline.u_agen_stage1.add_rel_out TOP.u_pipeline.u_agen_stage1.mux_disp_out TOP.u_pipeline.u_agen_stage1.mux_base_reg_out TOP.u_pipeline.u_agen_stage1.add_base_disp_out TOP.u_pipeline.u_agen_stage1.shf_sib_idx_out TOP.u_pipeline.u_agen_stage1.mux_sib_si_out TOP.u_pipeline.u_agen_stage1.add_sib_seg1_out TOP.u_pipeline.u_agen_stage1.mux_seg1_out TOP.u_pipeline.u_agen_stage1.sr3_size TOP.u_pipeline.u_agen_stage1.sib_i_size TOP.u_pipeline.u_agen_stage1.or_ints_out TOP.u_pipeline.u_agen_stage1.d2_mem_size_wb_bar TOP.u_pipeline.u_agen_stage1.and0_out TOP.u_pipeline.u_agen_stage1.and1_out TOP.u_pipeline.u_agen_stage1.or0_out TOP.u_pipeline.u_agen_stage1.or1_out TOP.u_pipeline.u_agen_stage1.mux_mm_a_hh_out TOP.u_pipeline.u_agen_stage1.mux_mm_a_hl_out TOP.u_pipeline.u_agen_stage1.mux_mm_a_lh_out TOP.u_pipeline.u_agen_stage1.mux_mm_a_ll_out TOP.u_pipeline.u_agen_stage1.mux_mm_cs_out TOP.u_pipeline.u_agen_stage1.mux_push_size_out TOP.u_pipeline.u_agen_stage1.mux_pop_size_out TOP.u_pipeline.u_agen_stage1.mux_sp_add_size_out TOP.u_pipeline.u_agen_stage1.Qprev_pop_size TOP.u_pipeline.u_agen_stage1.mux_push_add_out TOP.u_pipeline.u_agen_stage1.add_sp_out TOP.u_pipeline.u_agen_stage1.mux_temp_sp_out TOP.u_pipeline.u_agen_stage1.Qtemp_sp TOP.u_pipeline.u_agen_stage1.interrupt_status TOP.u_pipeline.u_agen_stage1.int_encode TOP.u_pipeline.u_agen_stage1.mux_int_addr_out TOP.u_pipeline.u_agen_stage1.DEP_V_IN TOP.u_pipeline.u_agen_stage1.or_exc_out TOP.u_pipeline.u_agen_stage1.or_jmp_stall_out }

# Global: Highlighting

# Global: Stack
gui_change_stack_mode -mode list

# Post database loading setting...

# Restore C1 time
gui_set_time -C1_only 222.167



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
catch {gui_list_expand -id ${Hier.1} TOP.u_pipeline}
catch {gui_list_select -id ${Hier.1} {TOP.u_pipeline.u_agen_stage1}}
gui_view_scroll -id ${Hier.1} -vertical -set 1480
gui_view_scroll -id ${Hier.1} -horizontal -set 0

# Data 'Data.1'
gui_list_set_filter -id ${Data.1} -list { {Buffer 1} {Input 1} {Others 1} {Linkage 1} {Output 1} {LowPower 1} {Parameter 1} {All 1} {Aggregate 1} {LibBaseMember 1} {Event 1} {Assertion 1} {Constant 1} {Interface 1} {BaseMembers 1} {Signal 1} {$unit 1} {Inout 1} {Variable 1} }
gui_list_set_filter -id ${Data.1} -text {*}
gui_list_show_data -id ${Data.1} {TOP.u_pipeline.u_agen_stage1}
gui_show_window -window ${Data.1}
catch { gui_list_select -id ${Data.1} {TOP.u_pipeline.u_agen_stage1.D2_MM1_NEEDED_AG }}
gui_view_scroll -id ${Data.1} -vertical -set 0
gui_view_scroll -id ${Data.1} -horizontal -set 0
gui_view_scroll -id ${Hier.1} -vertical -set 1480
gui_view_scroll -id ${Hier.1} -horizontal -set 0

# Source 'Source.1'
gui_src_value_annotate -id ${Source.1} -switch false
gui_set_env TOGGLE::VALUEANNOTATE 0
gui_open_source -id ${Source.1}  -replace -active TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.u_gpr_scoreboard_check_sr3 dependency_check/reg_scoreboard_check.v
gui_view_scroll -id ${Source.1} -vertical -set 0
gui_src_set_reusable -id ${Source.1}

# View 'Wave.1'
gui_wv_sync -id ${Wave.1} -switch false
set groupExD [gui_get_pref_value -category Wave -key exclusiveSG]
gui_set_pref_value -category Wave -key exclusiveSG -value {false}
set origWaveHeight [gui_get_pref_value -category Wave -key waveRowHeight]
gui_list_set_height -id Wave -height 25
set origGroupCreationState [gui_list_create_group_when_add -wave]
gui_list_create_group_when_add -wave -disable
gui_marker_create -id ${Wave.1} C2 130.67
gui_marker_set_ref -id ${Wave.1}  C1
gui_wv_zoom_timerange -id ${Wave.1} 0 287.985
gui_list_add_group -id ${Wave.1} -after {New Group} {Group8}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group9}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group10}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group11}
gui_list_add_group -id ${Wave.1}  -after TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.DEP_STALL {Group11|u_gpr_scoreboard_check_sr1}
gui_list_add_group -id ${Wave.1} -after Group11|u_gpr_scoreboard_check_sr1 {Group11|u_gpr_scoreboard_check_sr2}
gui_list_add_group -id ${Wave.1} -after Group11|u_gpr_scoreboard_check_sr2 {Group11|u_gpr_scoreboard_check_sr3}
gui_list_add_group -id ${Wave.1} -after Group11|u_gpr_scoreboard_check_sr3 {Group11|u_gpr_scoreboard_check_sr4}
gui_list_collapse -id ${Wave.1} Group11|u_gpr_scoreboard_check_sr1
gui_list_collapse -id ${Wave.1} Group11|u_gpr_scoreboard_check_sr2
gui_list_collapse -id ${Wave.1} Group11|u_gpr_scoreboard_check_sr3
gui_list_select -id ${Wave.1} {TOP.u_pipeline.ME2_GPR_SCOREBOARD_OUT }
gui_seek_criteria -id ${Wave.1} {Any Edge}


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
gui_list_set_insertion_bar  -id ${Wave.1} -group Group11|u_gpr_scoreboard_check_sr4  -position in

gui_marker_move -id ${Wave.1} {C1} 222.167
gui_view_scroll -id ${Wave.1} -vertical -set 0
gui_show_grid -id ${Wave.1} -enable false

# DriverLoad 'DriverLoad.1'
gui_get_drivers -session -id ${DriverLoad.1} -signal TOP.u_pipeline.AG_DEP_STALL_OUT -time 2.04 -starttime 110.32
gui_get_drivers -session -id ${DriverLoad.1} -signal TOP.u_pipeline.u_agen_stage1.dep_df_stall -time 0.94 -starttime 110.32
gui_get_drivers -session -id ${DriverLoad.1} -signal TOP.u_pipeline.u_agen_stage1.reg_dep_stall_out -time 1.69 -starttime 110.32
gui_get_drivers -session -id ${DriverLoad.1} -signal TOP.u_pipeline.u_agen_stage1.u_reg_dependency_check.DEP_STALL -time 1.69 -starttime 170.32

# View 'Wave.2'
gui_wv_sync -id ${Wave.2} -switch false
set groupExD [gui_get_pref_value -category Wave -key exclusiveSG]
gui_set_pref_value -category Wave -key exclusiveSG -value {false}
set origWaveHeight [gui_get_pref_value -category Wave -key waveRowHeight]
gui_list_set_height -id Wave -height 25
set origGroupCreationState [gui_list_create_group_when_add -wave]
gui_list_create_group_when_add -wave -disable
gui_marker_set_ref -id ${Wave.2}  C1
gui_wv_zoom_timerange -id ${Wave.2} 0 500
gui_list_add_group -id ${Wave.2} -after {New Group} {u_pipeline}
gui_seek_criteria -id ${Wave.2} {Any Edge}


gui_set_pref_value -category Wave -key exclusiveSG -value $groupExD
gui_list_set_height -id Wave -height $origWaveHeight
if {$origGroupCreationState} {
	gui_list_create_group_when_add -wave -enable
}
if { $groupExD } {
 gui_msg_report -code DVWW028
}
gui_list_set_filter -id ${Wave.2} -list { {Buffer 1} {Input 1} {Others 1} {Linkage 1} {Output 1} {Parameter 1} {All 1} {Aggregate 1} {LibBaseMember 1} {Event 1} {Assertion 1} {Constant 1} {Interface 1} {BaseMembers 1} {Signal 1} {$unit 1} {Inout 1} {Variable 1} }
gui_list_set_filter -id ${Wave.2} -text {*EXC*}
gui_list_set_insertion_bar  -id ${Wave.2} -group u_pipeline  -position in

gui_marker_move -id ${Wave.2} {C1} 222.167
gui_view_scroll -id ${Wave.2} -vertical -set 825
gui_show_grid -id ${Wave.2} -enable false

# View 'Wave.3'
gui_wv_sync -id ${Wave.3} -switch false
set groupExD [gui_get_pref_value -category Wave -key exclusiveSG]
gui_set_pref_value -category Wave -key exclusiveSG -value {false}
set origWaveHeight [gui_get_pref_value -category Wave -key waveRowHeight]
gui_list_set_height -id Wave -height 25
set origGroupCreationState [gui_list_create_group_when_add -wave]
gui_list_create_group_when_add -wave -disable
gui_marker_set_ref -id ${Wave.3}  C1
gui_wv_zoom_timerange -id ${Wave.3} 0 500
gui_list_add_group -id ${Wave.3} -after {New Group} {u_reg_dependency_check}
gui_list_add_group -id ${Wave.3}  -after u_reg_dependency_check {u_reg_dependency_check|u_agen_stage1}
gui_seek_criteria -id ${Wave.3} {Any Edge}



gui_set_env TOGGLE::DEFAULT_WAVE_WINDOW ${Wave.3}
gui_set_pref_value -category Wave -key exclusiveSG -value $groupExD
gui_list_set_height -id Wave -height $origWaveHeight
if {$origGroupCreationState} {
	gui_list_create_group_when_add -wave -enable
}
if { $groupExD } {
 gui_msg_report -code DVWW028
}
gui_list_set_filter -id ${Wave.3} -list { {Buffer 1} {Input 1} {Others 1} {Linkage 1} {Output 1} {Parameter 1} {All 1} {Aggregate 1} {LibBaseMember 1} {Event 1} {Assertion 1} {Constant 1} {Interface 1} {BaseMembers 1} {Signal 1} {$unit 1} {Inout 1} {Variable 1} }
gui_list_set_filter -id ${Wave.3} -text {*}
gui_list_set_insertion_bar  -id ${Wave.3} -group u_reg_dependency_check  -position in

gui_marker_move -id ${Wave.3} {C1} 222.167
gui_view_scroll -id ${Wave.3} -vertical -set 0
gui_show_grid -id ${Wave.3} -enable false
# Restore toplevel window zorder
# The toplevel window could be closed if it has no view/pane
if {[gui_exist_window -window ${TopLevel.1}]} {
	gui_set_active_window -window ${TopLevel.1}
	gui_set_active_window -window ${Source.1}
	gui_set_active_window -window ${HSPane.1}
}
if {[gui_exist_window -window ${TopLevel.4}]} {
	gui_set_active_window -window ${TopLevel.4}
	gui_set_active_window -window ${Wave.3}
}
if {[gui_exist_window -window ${TopLevel.3}]} {
	gui_set_active_window -window ${TopLevel.3}
	gui_set_active_window -window ${Wave.2}
}
if {[gui_exist_window -window ${TopLevel.2}]} {
	gui_set_active_window -window ${TopLevel.2}
	gui_set_active_window -window ${Wave.1}
}
#</Session>

