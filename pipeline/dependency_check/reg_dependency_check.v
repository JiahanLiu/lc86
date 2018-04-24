module reg_dependency_check (
   input STAGE_V,
  
   input [2:0] SR1_ID, SR2_ID, SR3_ID, SIB_I_ID, SEG1_ID, SEG2_ID,
   input [1:0] SR1_SIZE, SR2_SIZE, SR3_SIZE, SIB_I_SIZE,
   input SR1_NEEDED, SR2_NEEDED, SR3_NEEDED, SIB_I_NEEDED, 
   input SEG1_NEEDED, SEG2_NEEDED, MM1_NEEDED, MM2_NEEDED,

   input ME_V,
   input [23:0] ME_GPR_SCOREBOARD,
   input [7:0] ME_SEG_SCOREBOARD,
   input [7:0] ME_MM_SCOREBOARD,

   input EX_V,
   input [23:0] EX_GPR_SCOREBOARD,
   input [7:0] EX_SEG_SCOREBOARD,
   input [7:0] EX_MM_SCOREBOARD,

   output DEP_STALL
);

   wire [23:0] and0_out, and3_out;
   wire [7:0] and1_out, and2_out, and4_out, and5_out;

   wire [23:0] or0_out;
   wire [7:0] or1_out, or2_out;
   wire or3_out, or4_out, or5_out, or6_out;

   and2$
      and0 [23:0] (and0_out, ME_V, ME_GPR_SCOREBOARD),
      and1 [7:0] (and1_out, ME_V, ME_SEG_SCOREBOARD),
      and2 [7:0] (and2_out, ME_V, ME_MM_SCOREBOARD);

   and2$
      and3 [23:0] (and3_out, EX_V, EX_GPR_SCOREBOARD),
      and4 [7:0] (and4_out, EX_V, EX_SEG_SCOREBOARD),
      and5 [7:0] (and5_out, EX_V, EX_MM_SCOREBOARD);

   or2$
      or0 [23:0] (or0_out, and0_out, and3_out),
      or1 [7:0] (or1_out, and1_out, and4_out),
      or2 [7:0] (or2_out, and2_out, and5_out);

   wire [23:0] gpr_scoreboard;
   wire [7:0] seg_scoreboard, mm_scoreboard;

   assign gpr_scoreboard = or0_out;
   assign seg_scoreboard = or1_out;
   assign mm_scoreboard = or2_out;

   reg_scoreboard_check
      u_reg_scoreboard_check_seg1 (STAGE_V, SEG1_NEEDED, SEG1_ID, seg_scoreboard, seg1_stall),
      u_reg_scoreboard_check_seg2 (STAGE_V, SEG2_NEEDED, SEG2_ID, seg_scoreboard, seg2_stall),

      u_reg_scoreboard_check_mm1 (STAGE_V, MM1_NEEDED, SR1_ID, mm_scoreboard, mm1_stall),
      u_reg_scoreboard_check_mm2 (STAGE_V, MM2_NEEDED, SR2_ID, mm_scoreboard, mm2_stall);

   gpr_scoreboard_check
      u_gpr_scoreboard_check_sr1 (STAGE_V, SR1_NEEDED, SR1_ID, SR1_SIZE, gpr_scoreboard, sr1_stall),
      u_gpr_scoreboard_check_sr2 (STAGE_V, SR2_NEEDED, SR2_ID, SR2_SIZE, gpr_scoreboard, sr2_stall),
      u_gpr_scoreboard_check_sr3 (STAGE_V, SR3_NEEDED, SR3_ID, SR3_SIZE, gpr_scoreboard, sr3_stall),
      u_gpr_scoreboard_check_sr4 (STAGE_V, SIB_I_NEEDED, SIB_I_ID, SIB_I_SIZE, gpr_scoreboard, sr4_stall);

   or2$ or3 (or3_out, seg1_stall, seg2_stall);
   or3$ or4 (or4_out, mm1_stall, mm2_stall, sr1_stall);
   or3$ or5 (or5_out, sr2_stall, sr3_stall, sr4_stall);
   or3$ or6 (or6_out, or3_out, or4_out, or5_out);
   assign DEP_STALL = or6_out;

endmodule
 
