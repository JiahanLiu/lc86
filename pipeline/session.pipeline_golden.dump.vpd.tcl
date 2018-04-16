# Begin_DVE_Session_Save_Info
# DVE full session
# Saved on Sun Apr 15 16:09:01 2018
# Designs open: 1
#   V1: pipeline.dump.vpd
# Toplevel windows open: 2
# 	TopLevel.1
# 	TopLevel.2
#   Source.1: TOP.u_pipeline.u_register_file.gpr
#   Wave.1: 11 signals
#   Group count = 1
#   Group Group1 signal count = 11
# End_DVE_Session_Save_Info

# DVE version: K-2015.09-SP1_Full64
# DVE build date: Nov 24 2015 21:15:24


#<Session mode="Full" path="/home/ecelrc/students/anarkhede/micro/lc86/pipeline/session.pipeline.dump.vpd.tcl" type="Debug">

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
gui_show_window -window ${TopLevel.1} -show_state normal -rect {{150 157} {1182 999}}

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
set HSPane.1 [gui_create_window -type HSPane -parent ${TopLevel.1} -dock_state left -dock_on_new_line true -dock_extent 186]
catch { set Hier.1 [gui_share_window -id ${HSPane.1} -type Hier] }
gui_set_window_pref_key -window ${HSPane.1} -key dock_width -value_type integer -value 186
gui_set_window_pref_key -window ${HSPane.1} -key dock_height -value_type integer -value -1
gui_set_window_pref_key -window ${HSPane.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${HSPane.1} {{left 0} {top 0} {width 185} {height 584} {dock_state left} {dock_on_new_line true} {child_hier_colhier 140} {child_hier_coltype 100} {child_hier_colpd 0} {child_hier_col1 0} {child_hier_col2 1} {child_hier_col3 -1}}
set DLPane.1 [gui_create_window -type DLPane -parent ${TopLevel.1} -dock_state left -dock_on_new_line true -dock_extent 327]
catch { set Data.1 [gui_share_window -id ${DLPane.1} -type Data] }
gui_set_window_pref_key -window ${DLPane.1} -key dock_width -value_type integer -value 327
gui_set_window_pref_key -window ${DLPane.1} -key dock_height -value_type integer -value 584
gui_set_window_pref_key -window ${DLPane.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${DLPane.1} {{left 0} {top 0} {width 326} {height 584} {dock_state left} {dock_on_new_line true} {child_data_colvariable 182} {child_data_colvalue 100} {child_data_coltype 56} {child_data_col1 0} {child_data_col2 1} {child_data_col3 2}}
set Console.1 [gui_create_window -type Console -parent ${TopLevel.1} -dock_state bottom -dock_on_new_line true -dock_extent 152]
gui_set_window_pref_key -window ${Console.1} -key dock_width -value_type integer -value 1033
gui_set_window_pref_key -window ${Console.1} -key dock_height -value_type integer -value 152
gui_set_window_pref_key -window ${Console.1} -key dock_offset -value_type integer -value 0
gui_update_layout -id ${Console.1} {{left 0} {top 0} {width 1032} {height 151} {dock_state bottom} {dock_on_new_line true}}
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
gui_show_window -window ${TopLevel.2} -show_state normal -rect {{591 239} {2046 921}}

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
gui_update_layout -id ${Wave.1} {{show_state maximized} {dock_state undocked} {dock_on_new_line false} {child_wave_left 422} {child_wave_right 1028} {child_wave_colname 209} {child_wave_colvalue 209} {child_wave_col1 0} {child_wave_col2 1}}

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
gui_set_time_units 1ps
#</Database>

# DVE Global setting session: 


# Global: Bus

# Global: Expressions

# Global: Signal Time Shift

# Global: Signal Compare

# Global: Signal Groups


set _session_group_1 Group1
gui_sg_create "$_session_group_1"
set Group1 "$_session_group_1"

# Decode stage 1 signals 
gui_sg_addsignal -group "$_session_group_1" { \
TOP.u_pipeline.CLK \
TOP.u_pipeline.u_decode_stage1.opcode \
TOP.u_pipeline.u_decode_stage1.opcode_size \
TOP.u_pipeline.u_decode_stage1.modrm_sel \
TOP.u_pipeline.u_decode_stage1.instr_length_updt \
TOP.u_pipeline.u_decode_stage1.prefix_size \
TOP.u_pipeline.u_decode_stage1.prefix_present \
TOP.u_pipeline.u_decode_stage1.segment_override \
TOP.u_pipeline.u_decode_stage1.operand_override \
TOP.u_pipeline.u_decode_stage1.repeat_prefix \
TOP.u_pipeline.u_decode_stage1.modrm_present \
TOP.u_pipeline.u_decode_stage1.imm_present \
TOP.u_pipeline.u_decode_stage1.imm_size \
TOP.u_pipeline.u_decode_stage1.sib_present \
TOP.u_pipeline.u_decode_stage1.disp_present \
TOP.u_pipeline.u_decode_stage1.disp_size \
TOP.u_pipeline.u_decode_stage1.imm_sel \
TOP.u_pipeline.u_decode_stage1.disp_sel \
TOP.u_pipeline.u_decode_stage1.offset_present \
TOP.u_pipeline.u_decode_stage1.offset_size \
TOP.u_pipeline.u_decode_stage1.segID \
TOP.u_pipeline.u_decode_stage1.modrm \
TOP.u_pipeline.u_decode_stage1.sib \
}

# Decode_stage 2 signals
set _session_group_2 Group2
gui_sg_create "$_session_group_2"
set Group2 "$_session_group_2"

gui_sg_addsignal -group "$_session_group_2" { \
TOP.u_pipeline.CLK \
TOP.u_pipeline.u_decode_stage2.offset \
TOP.u_pipeline.u_decode_stage2.CONTROL_STORE \
TOP.u_pipeline.u_decode_stage2.D2_DATA_SIZE_AG \
TOP.u_pipeline.u_decode_stage2.D2_SR1_NEEDED_AG \
TOP.u_pipeline.u_decode_stage2.D2_SEG1_NEEDED_AG \
TOP.u_pipeline.u_decode_stage2.D2_MM1_NEEDED_AG \
TOP.u_pipeline.u_decode_stage2.D2_MEM_RD_ME \
TOP.u_pipeline.u_decode_stage2.D2_MEM_WR_ME \
TOP.u_pipeline.u_decode_stage2.D2_ALUK_EX \
TOP.u_pipeline.u_decode_stage2.D2_LD_GPR1_WB \
TOP.u_pipeline.u_decode_stage2.D2_LD_MM_WB \
TOP.u_pipeline.u_decode_stage2.SR1_OUT \
TOP.u_pipeline.u_decode_stage2.SR2_OUT \
TOP.u_pipeline.u_decode_stage2.SR3_OUT \
TOP.u_pipeline.u_decode_stage2.SR4_OUT \
TOP.u_pipeline.u_decode_stage2.SEG1_OUT \
TOP.u_pipeline.u_decode_stage2.SEG2_OUT \
TOP.u_pipeline.u_decode_stage2.IMM32_OUT \
TOP.u_pipeline.u_decode_stage2.DISP32_OUT \
TOP.u_pipeline.u_decode_stage2.DE_SIB_EN_AG \
TOP.u_pipeline.u_decode_stage2.DE_DISP_EN_AG \
TOP.u_pipeline.u_decode_stage2.DE_BASE_REG_EN_AG \
TOP.u_pipeline.u_decode_stage2.DE_MUX_SEG_AG \
TOP.u_pipeline.u_decode_stage2.DE_CMPXCHG_AG \
TOP.u_pipeline.u_decode_stage2.DE_SIB_S_AG \
}

# Register file signals
set _session_group_3 Group3
gui_sg_create "$_session_group_3"
set Group3 "$_session_group_3"

gui_sg_addsignal -group "$_session_group_3" { \
TOP.u_pipeline.CLK \
TOP.u_pipeline.SR1_DATA \
TOP.u_pipeline.SR2_DATA \
TOP.u_pipeline.SR3_DATA \
TOP.u_pipeline.SIB_I_DATA \
TOP.u_pipeline.u_register_file.SEGDOUT1 \
TOP.u_pipeline.u_register_file.SEGDOUT2 \
TOP.u_pipeline.u_register_file.MMDOUT1 \
TOP.u_pipeline.u_register_file.MMDOUT2 \
TOP.u_pipeline.u_register_file.CSDOUT \
TOP.u_pipeline.u_register_file.EIPDOUT \
TOP.u_pipeline.u_register_file.EFLAGSDOUT \
}

# Address generation stage signals
set _session_group_4 Group4
gui_sg_create "$_session_group_4"
set Group4 "$_session_group_4"

gui_sg_addsignal -group "$_session_group_4" { \
TOP.u_pipeline.CLK \
TOP.u_pipeline.u_address_generation.SR1_OUT \
TOP.u_pipeline.u_address_generation.SR2_OUT \
TOP.u_pipeline.u_address_generation.SR3_OUT \
TOP.u_pipeline.u_address_generation.SIB_I_OUT \
TOP.u_pipeline.u_address_generation.SEG1_OUT \
TOP.u_pipeline.u_address_generation.SEG2_OUT \
TOP.u_pipeline.u_address_generation.MM1_OUT \
TOP.u_pipeline.u_address_generation.MM2_OUT \
TOP.u_pipeline.u_address_generation.DATA_SIZE_OUT \
TOP.u_pipeline.u_address_generation.NEIP_OUT \
TOP.u_pipeline.u_address_generation.NCS_OUT \
TOP.u_pipeline.u_address_generation.CONTROL_STORE_OUT \
TOP.u_pipeline.u_address_generation.A_OUT \
TOP.u_pipeline.u_address_generation.B_OUT \
TOP.u_pipeline.u_address_generation.MM_A_OUT \
TOP.u_pipeline.u_address_generation.MM_B_OUT \
TOP.u_pipeline.u_address_generation.SP_XCHG_DATA_OUT \
TOP.u_pipeline.u_address_generation.MEM_RD_ADDR_OUT \
TOP.u_pipeline.u_address_generation.MEM_WB_ADDR_OUT \
TOP.u_pipeline.u_address_generation.D2_ALUK_EX_OUT \
TOP.u_pipeline.u_address_generation.DRID1_OUT \
TOP.u_pipeline.u_address_generation.DRID2_OUT \
TOP.u_pipeline.u_address_generation.D2_MEM_RD_ME_OUT \
TOP.u_pipeline.u_address_generation.D2_MEM_WR_WB_OUT \
TOP.u_pipeline.u_address_generation.D2_LD_GPR1_WB_OUT \
TOP.u_pipeline.u_address_generation.D2_LD_MM_WB_OUT \
TOP.u_pipeline.u_address_generation.DEP_STALL_OUT \
TOP.u_pipeline.u_address_generation.SEG_LIMIT_EXC_OUT \
}

# MEMORY STAGE SIGNALS
set _session_group_5 Group5
gui_sg_create "$_session_group_5"
set Group5 "$_session_group_5"

gui_sg_addsignal -group "$_session_group_5" { \
TOP.u_pipeline.CLK \
TOP.u_pipeline.u_memory_stage.DCACHE_EN \
TOP.u_pipeline.u_memory_stage.NEIP_OUT \
TOP.u_pipeline.u_memory_stage.NCS_OUT \
TOP.u_pipeline.u_memory_stage.CONTROL_STORE_OUT \
TOP.u_pipeline.u_memory_stage.A_OUT \
TOP.u_pipeline.u_memory_stage.B_OUT \
TOP.u_pipeline.u_memory_stage.MM_A_OUT \
TOP.u_pipeline.u_memory_stage.MM_B_OUT \
TOP.u_pipeline.u_memory_stage.SP_XCHG_DATA_OUT \
TOP.u_pipeline.u_memory_stage.MEM_RD_ADDR_OUT \
TOP.u_pipeline.u_memory_stage.MEM_WR_ADDR_OUT \
TOP.u_pipeline.u_memory_stage.DATA_SIZE_OUT \
TOP.u_pipeline.u_memory_stage.DE_ALUK_EX_OUT \
TOP.u_pipeline.u_memory_stage.DRID1_OUT \
TOP.u_pipeline.u_memory_stage.DRID2_OUT \
TOP.u_pipeline.u_memory_stage.D2_MEM_WR_WB_OUT \
TOP.u_pipeline.u_memory_stage.D2_LD_GPR1_WB_OUT \
TOP.u_pipeline.u_memory_stage.D2_LD_MM_WB_OUT \
}


# EXECUTE STAGE SIGNALS
set _session_group_6 Group6
gui_sg_create "$_session_group_6"
set Group6 "$_session_group_6"

gui_sg_addsignal -group "$_session_group_6" {
TOP.u_pipeline.CLK \
TOP.u_pipeline.u_execute.WB_V_next \
TOP.u_pipeline.u_execute.WB_NEIP_next \
TOP.u_pipeline.u_execute.WB_NCS_next \
TOP.u_pipeline.u_execute.WB_CONTROL_STORE_next \
TOP.u_pipeline.u_execute.WB_de_datasize_all_next \
TOP.u_pipeline.u_execute.WB_de_aluk_ex_next \
TOP.u_pipeline.u_execute.WB_de_ld_gpr1_wb_next \
TOP.u_pipeline.u_execute.WB_de_dcache_write_wb_next \
TOP.u_pipeline.u_execute.WB_de_flags_affected_wb_next \
TOP.u_pipeline.u_execute.WB_ALU32_RESULT_next \
TOP.u_pipeline.u_execute.WB_FLAGS_next \
TOP.u_pipeline.u_execute.WB_CMPS_POINTER_next \
TOP.u_pipeline.u_execute.WB_COUNT_next \
TOP.u_pipeline.u_execute.WB_DR1_next \
TOP.u_pipeline.u_execute.WB_DR2_next \
TOP.u_pipeline.u_execute.WB_DR3_next \
}

# WRITEBACK SIGNALS
set _session_group_7 Group7
gui_sg_create "$_session_group_7"
set Group7 "$_session_group_7"

gui_sg_addsignal -group "$_session_group_7" { \
TOP.u_pipeline.CLK \
TOP.u_pipeline.u_writeback.Out_DR1 \
TOP.u_pipeline.u_writeback.Out_DR2 \
TOP.u_pipeline.u_writeback.Out_DR3 \
TOP.u_pipeline.u_writeback.Out_DR1_Data \
TOP.u_pipeline.u_writeback.Out_DR2_Data \
TOP.u_pipeline.u_writeback.Out_DR3_Data \
TOP.u_pipeline.u_writeback.out_v_de_ld_gpr1_wb \
TOP.u_pipeline.u_writeback.out_v_cs_ld_gpr2_wb \
TOP.u_pipeline.u_writeback.out_v_cs_ld_gpr3_wb \
TOP.u_pipeline.u_writeback.out_de_datasize \
TOP.u_pipeline.u_writeback.Out_Dcache_Data \
TOP.u_pipeline.u_writeback.Out_Dcache_Address \
TOP.u_pipeline.u_writeback.Out_ex_repne_termination_all \
}


# Global: Highlighting

# Global: Stack
gui_change_stack_mode -mode list

# Post database loading setting...

# Restore C1 time
gui_set_time -C1_only 140712



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
catch {gui_list_expand -id ${Hier.1} TOP.u_pipeline.u_register_file}
catch {gui_list_select -id ${Hier.1} {TOP.u_pipeline.u_register_file.gpr}}
gui_view_scroll -id ${Hier.1} -vertical -set 1120
gui_view_scroll -id ${Hier.1} -horizontal -set 0

# Data 'Data.1'
gui_list_set_filter -id ${Data.1} -list { {Buffer 1} {Input 1} {Others 1} {Linkage 1} {Output 1} {LowPower 1} {Parameter 1} {All 1} {Aggregate 1} {LibBaseMember 1} {Event 1} {Assertion 1} {Constant 1} {Interface 1} {BaseMembers 1} {Signal 1} {$unit 1} {Inout 1} {Variable 1} }
gui_list_set_filter -id ${Data.1} -text {*}
gui_list_show_data -id ${Data.1} {TOP.u_pipeline.u_register_file.gpr}
gui_view_scroll -id ${Data.1} -vertical -set 0
gui_view_scroll -id ${Data.1} -horizontal -set 0
gui_view_scroll -id ${Hier.1} -vertical -set 1120
gui_view_scroll -id ${Hier.1} -horizontal -set 0

# Source 'Source.1'
gui_src_value_annotate -id ${Source.1} -switch false
gui_set_env TOGGLE::VALUEANNOTATE 0
gui_open_source -id ${Source.1}  -replace -active TOP.u_pipeline.u_register_file.gpr common/cache_and_registers/registers.v
gui_view_scroll -id ${Source.1} -vertical -set 5706
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
gui_wv_zoom_timerange -id ${Wave.1} 0 219904
gui_list_add_group -id ${Wave.1} -after {New Group} {Group1}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group2}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group3}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group4}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group5}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group6}
gui_list_add_group -id ${Wave.1} -after {New Group} {Group7}
gui_list_select -id ${Wave.1} {TOP.u_pipeline.u_register_file.gpr.reg1_ll_out }
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
gui_list_set_insertion_bar  -id ${Wave.1} -group Group1  -item {TOP.u_pipeline.u_register_file.gpr.reg1_ll_out[31:0]} -position below

gui_marker_move -id ${Wave.1} {C1} 140712
gui_view_scroll -id ${Wave.1} -vertical -set 0
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

