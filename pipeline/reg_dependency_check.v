
module cmp_regid (OUT, REG1, REG2, V_LD_REG2);
   input [2:0] REG1, REG2;
   input V_LD_REG2;

   output OUT;

   wire [2:0] xnor_out;

   xnor2$ xnor0 [2:0] (xnor_out, REG1, REG2);
   and4$ and0 (OUT, xnor_out[0], xnor_out[1], xnor_out[2], V_LD_REG2);

endmodule;

module chk_needed (
   input [2:0] REG,
   input [2:0] S1_DRID, S2_DRID, S3_DRID,

   input V_S1_LD_REG, V_S2_LD_REG, V_S3_LD_REG,
   input REG_NEEDED, STAGE_V,

   output OUT
);

   wire and_v_reg_needed_out;

   cmp_regid 
      cmp_reg_s1_drid (cmp_reg_s1_drid_out, REG, S1_DRID, V_S1_LD_REG),
      cmp_reg_s2_drid (cmp_reg_s2_drid_out, REG, S2_DRID, V_S2_LD_REG),
      cmp_reg_s3_drid (cmp_reg_s3_drid_out, REG, S3_DRID, V_S3_LD_REG);

   and2$
      and_v_reg_needed (and_v_reg_needed_out, REG_NEEDED, STAGE_V);

   and4$
      and_reg_needed (OUT, and_v_reg_needed_out, cmp_reg_s1_drid_out, cmp_reg_s2_drid_out, cmp_reg_s3_drid_out);

endmodule

module reg_dependency_check (
   input STAGE_V,
  
   input [2:0] SR1_ID, SR2_ID, SR3_ID, SIB_I_ID, SEG1_ID, SEG2_ID,
   input SR1_NEEDED, SR2_NEEDED, SR3_NEEDED, SIB_I_NEEDED, 
   input SEG1_NEEDED, SEG2_NEEDED, MM1_NEEDED, MM2_NEEDED,

   input [2:0] AG_DRID1, AG_DRID2,
   input V_AG_LD_GPR1, V_AG_LD_GPR2, V_AG_LD_SEG, V_AG_LD_CSEG, V_AG_LD_MM,

   input [2:0] ME_DRID1, ME_DRID2,
   input V_ME_LD_GPR1, V_ME_LD_GPR2, V_ME_LD_SEG, V_ME_LD_CSEG, V_ME_LD_MM,

   input [2:0] EX_DRID1, EX_DRID2,
   input V_EX_LD_GPR1, V_EX_LD_GPR2, V_EX_LD_SEG, V_EX_LD_CSEG, V_EX_LD_MM,

   output DEP_STALL
);

   // Compare SEG1, SEG2 only with DRID1
   /* (SEG1_ID == AG_DRID1 AND V_AG_LD_SEG) || (SEG1_ID == ME_DRID1 AND V_ME_LD_SEG) || (SEG1_ID == EX_DRID1 AND V_EX_LD_SEG) AND SEG1_NEEDED
   || (SEG2_ID == AG_DRID1 AND V_AG_LD_SEG) || (SEG2_ID == ME_DRID1 AND V_ME_LD_SEG) || (SEG2_ID == EX_DRID1 AND V_EX_LD_SEG) AND SEG2_NEEDED
   || (SR1_ID == AG_DRID1 AND V_AG_LD_GPR1) ... AND SR1_NEEDED || (SR1_ID == AG_DRID2 AND V_AG_LD_GPR2) ... AND SR1_NEEDED
   || (SR2_ID == AG_DRID1 AND V_AG_LD_GPR1) ... AND SR2_NEEDED || (SR2_ID == AG_DRID2 AND V_AG_LD_GPR2) ... AND SR2_NEEDED
   || (SR3_ID == AG_DRID1 AND V_AG_LD_GPR1) ... AND SR3_NEEDED || (SR3_ID == AG_DRID2 AND V_AG_LD_GPR2) ... AND SR3_NEEDED
   || (SIB_I_ID == AG_DRID1 AND V_AG_LD_GPR1) ... AND SIB_I_NEEDED || (SIB_I_ID == AG_DRID2 AND V_AG_LD_GPR2) ... AND SIB_I_NEEDED
   || (SR1_ID == AG_DRID1 AND V_AG_LD_MM) ... AND MM1_NEEDED
   || (SR2_ID == AG_DRID1 AND V_AG_LD_MM) ... AND MM2_NEEDED
    */
   wire [2:0] buf_seg1, buf_seg2, buf_sr1, buf_sr2, buf_sr3, buf_sib_i;
   wire [2:0] buf_ag_drid1, buf_ag_drid2, buf_me_drid1, buf_me_drid2, buf_ex_drid1, buf_ex_drid2;
   wire       buf_stage_v;

   bufferH16$ 
      bufferH16_seg1 [2:0] (buf_seg1, SEG1_ID),
      bufferH16_seg2 [2:0] (buf_seg2, SEG2_ID),
      bufferH16_sr1 [2:0] (buf_sr1, SR1_ID),
      bufferH16_sr2 [2:0] (buf_sr2, SR2_ID),
      bufferH16_sr3 [2:0] (buf_sr3, SR3_ID),
      bufferH16_sib_i [2:0] (buf_sib_i, SIB_I_ID),

      bufferH16_ag_drid1 [2:0] (buf_ag_drid1, AG_DRID1),
      bufferH16_ag_drid2 [2:0] (buf_ag_drid2, AG_DRID2),
      bufferH16_me_drid1 [2:0] (buf_me_drid1, ME_DRID1),
      bufferH16_me_drid2 [2:0] (buf_me_drid2, ME_DRID2),
      bufferH16_ex_drid1 [2:0] (buf_ex_drid1, EX_DRID1),
      bufferH16_ex_drid2 [2:0] (buf_ex_drid2, EX_DRID2),

      bufferH16_stage_v [2:0] (buf_stage_v, STAGE_V);

   or2$ 
      or_ag_seg_cseg (or_ag_seg_cseg_out, V_AG_LD_SEG, V_AG_LD_CSEG),
      or_me_seg_cseg (or_me_seg_cseg_out, V_ME_LD_SEG, V_ME_LD_CSEG),
      or_ex_seg_cseg (or_ex_seg_cseg_out, V_EX_LD_SEG, V_EX_LD_CSEG);

   chk_needed
      u_chk_seg1 (buf_seg1, buf_ag_drid1, buf_me_drid1, buf_ex_drid1, or_ag_seg_cseg_out, or_me_seg_cseg_out, or_ex_seg_cseg_out, SEG1_NEEDED, buf_stage_v, u_chk_seg1_out),
      u_chk_seg2 (buf_seg2, buf_ag_drid1, buf_me_drid1, buf_ex_drid1, or_ag_seg_cseg_out, or_me_seg_cseg_out, or_ex_seg_cseg_out, SEG2_NEEDED, buf_stage_v, u_chk_seg2_out);
   
   chk_needed 
      u_chk_sr1_gpr1 (buf_sr1, buf_ag_drid1, buf_me_drid1, buf_ex_drid1, V_AG_LD_GPR1, V_ME_LD_GPR1, V_EX_LD_GPR1, SR1_NEEDED, buf_stage_v, u_chk_sr1_gpr1_out),
      u_chk_sr1_gpr2 (buf_sr1, buf_ag_drid2, buf_me_drid2, buf_ex_drid2, V_AG_LD_GPR2, V_ME_LD_GPR2, V_EX_LD_GPR2, SR1_NEEDED, buf_stage_v, u_chk_sr1_gpr2_out);

   chk_needed 
      u_chk_sr2_gpr1 (buf_sr2, buf_ag_drid1, buf_me_drid1, buf_ex_drid1, V_AG_LD_GPR1, V_ME_LD_GPR1, V_EX_LD_GPR1, SR2_NEEDED, buf_stage_v, u_chk_sr2_gpr1_out),
      u_chk_sr2_gpr2 (buf_sr2, buf_ag_drid2, buf_me_drid2, buf_ex_drid2, V_AG_LD_GPR2, V_ME_LD_GPR2, V_EX_LD_GPR2, SR2_NEEDED, buf_stage_v, u_chk_sr2_gpr2_out);

   chk_needed 
      u_chk_sr3_gpr1 (buf_sr3, buf_ag_drid1, buf_me_drid1, buf_ex_drid1, V_AG_LD_GPR1, V_ME_LD_GPR1, V_EX_LD_GPR1, SR3_NEEDED, buf_stage_v, u_chk_sr3_gpr1_out),
      u_chk_sr3_gpr2 (buf_sr3, buf_ag_drid2, buf_me_drid2, buf_ex_drid2, V_AG_LD_GPR2, V_ME_LD_GPR2, V_EX_LD_GPR2, SR3_NEEDED, buf_stage_v, u_chk_sr3_gpr2_out);

   chk_needed 
      u_chk_sr4_gpr1 (buf_sib_i, buf_ag_drid1, buf_me_drid1, buf_ex_drid1, V_AG_LD_GPR1, V_ME_LD_GPR1, V_EX_LD_GPR1, SIB_I_NEEDED, buf_stage_v, u_chk_sr4_gpr1_out),
      u_chk_sr4_gpr2 (buf_sib_i, buf_ag_drid2, buf_me_drid2, buf_ex_drid2, V_AG_LD_GPR2, V_ME_LD_GPR2, V_EX_LD_GPR2, SIB_I_NEEDED, buf_stage_v, u_chk_sr4_gpr2_out);

   chk_needed 
      u_chk_mm1 (buf_sr1, buf_ag_drid1, buf_me_drid1, buf_ex_drid1, V_AG_LD_MM, V_ME_LD_MM, V_EX_LD_MM, MM1_NEEDED, buf_stage_v, u_chk_mm1_out),
      u_chk_mm2 (buf_sr2, buf_ag_drid1, buf_me_drid1, buf_ex_drid1, V_AG_LD_MM, V_ME_LD_MM, V_EX_LD_MM, MM2_NEEDED, buf_stage_v, u_chk_mm2_out);

   or4$
      or_chk1 (or_chk1_out, u_chk_seg1_out, u_chk_seg2_out, u_chk_sr1_gpr1_out, u_chk_sr1_gpr2_out),
      or_chk2 (or_chk2_out, u_chk_sr2_gpr1_out, u_chk_sr2_gpr2_out, u_chk_sr3_gpr1_out, u_chk_sr3_gpr2_out),
      or_chk3 (or_chk3_out, u_chk_sr4_gpr1_out, u_chk_sr4_gpr2_out, u_chk_mm1_out, u_chk_mm2_out);

   or3$
      or_chk4 (DEP_STALL, or_chk1_out, or_chk2_out, or_chk3_out);
/*
   or2$ 
      or_ag_seg_cseg (or_ag_seg_cseg_out, V_AG_LD_SEG, V_AG_LD_CSEG),
      or_me_seg_cseg (or_me_seg_cseg_out, V_ME_LD_SEG, V_ME_LD_CSEG),
      or_ex_seg_cseg (or_ex_seg_cseg_out, V_EX_LD_SEG, V_EX_LD_CSEG);

      cmp_seg2_ag_drid1 (cmp_seg2_ag_drid1_out, SEG2_ID, AG_DRID1, or_seg_cseg_out2),
      cmp_seg2_me_drid1 (cmp_seg2_me_drid1_out, SEG2_ID, ME_DRID1, or_seg_cseg_out2),
      cmp_seg2_ex_drid1 (cmp_seg2_ex_drid1_out, SEG2_ID, EX_DRID1, or_seg_cseg_out2);

      and_seg2_needed (and_seg2_needed_out, SEG2_NEEDED, cmp_seg2_ag_drid1_out, cmp_seg2_me_drid1_out, cmp_seg2_ex_drid1_out);
*/
 
/*
   cmp_regid
      cmp_sr1_ag_drid1 (cmp_sr1_ag_drid1_out, SR1_ID, AG_DRID1, V_AG_LD_GPR1),
      cmp_sr1_me_drid1 (cmp_sr1_me_drid1_out, SR1_ID, ME_DRID1, V_ME_LD_GPR1),
      cmp_sr1_ex_drid1 (cmp_sr1_ex_drid1_out, SR1_ID, EX_DRID1, V_EX_LD_GPR1),
      cmp_sr1_ag_drid2 (cmp_sr1_ag_drid2_out, SR1_ID, AG_DRID2, V_AG_LD_GPR2),
      cmp_sr1_me_drid2 (cmp_sr1_me_drid2_out, SR1_ID, ME_DRID2, V_ME_LD_GPR2),
      cmp_sr1_ex_drid2 (cmp_sr1_ex_drid2_out, SR1_ID, EX_DRID2, V_EX_LD_GPR2);

   and2$
      and_sr1_needed (and_sr1_needed_out, SR1_NEEDED, cmp_sr1_ag_drid1_out, cmp_sr1_me_drid1_out, cmp_sr1_ex_drid1_out),
      and_sr1_needed2 (and_sr1_needed_out2, SR1_NEEDED, cmp_sr1_ag_drid2_out, cmp_sr1_me_drid2_out, cmp_sr1_ex_drid2_out);
*/

/*
   cmp_regid
      cmp_sr2_ag_drid1 (cmp_sr2_ag_drid1_out, SR2_ID, AG_DRID1, V_AG_LD_GPR1),
      cmp_sr2_me_drid1 (cmp_sr2_me_drid1_out, SR2_ID, ME_DRID1, V_ME_LD_GPR1),
      cmp_sr2_ex_drid1 (cmp_sr2_ex_drid1_out, SR2_ID, EX_DRID1, V_EX_LD_GPR1),
      cmp_sr2_ag_drid2 (cmp_sr2_ag_drid2_out, SR2_ID, AG_DRID2, V_AG_LD_GPR2),
      cmp_sr2_me_drid2 (cmp_sr2_me_drid2_out, SR2_ID, ME_DRID2, V_ME_LD_GPR2),
      cmp_sr2_ex_drid2 (cmp_sr2_ex_drid2_out, SR2_ID, EX_DRID2, V_EX_LD_GPR2);

   and2$
      and_sr2_needed (and_sr2_needed_out, SR2_NEEDED, cmp_sr2_ag_drid1_out, cmp_sr2_me_drid1_out, cmp_sr2_ex_drid1_out),
      and_sr2_needed2 (and_sr2_needed_out2, SR2_NEEDED, cmp_sr2_ag_drid2_out, cmp_sr2_me_drid2_out, cmp_sr2_ex_drid2_out);
*/
/*
   cmp_regid
      cmp_sr3_ag_drid1 (cmp_sr3_ag_drid1_out, SR3_ID, AG_DRID1, V_AG_LD_GPR1),
      cmp_sr3_me_drid1 (cmp_sr3_me_drid1_out, SR3_ID, ME_DRID1, V_ME_LD_GPR1),
      cmp_sr3_ex_drid1 (cmp_sr3_ex_drid1_out, SR3_ID, EX_DRID1, V_EX_LD_GPR1),
      cmp_sr3_ag_drid2 (cmp_sr3_ag_drid2_out, SR3_ID, AG_DRID2, V_AG_LD_GPR2),
      cmp_sr3_me_drid2 (cmp_sr3_me_drid2_out, SR3_ID, ME_DRID2, V_ME_LD_GPR2),
      cmp_sr3_ex_drid2 (cmp_sr3_ex_drid2_out, SR3_ID, EX_DRID2, V_EX_LD_GPR2);

   and2$
      and_sr3_needed (and_sr3_needed_out, SR3_NEEDED, cmp_sr1_ag_drid1_out, cmp_sr1_me_drid1_out, cmp_sr1_ex_drid1_out),
      and_sr3_needed2 (and_sr3_needed_out2, SR3_NEEDED, cmp_sr1_ag_drid2_out, cmp_sr1_me_drid2_out, cmp_sr1_ex_drid2_out);
*/
/*
      cmp_sr4_ag_drid1 (cmp_sr4_ag_drid1_out, SIB_I_ID, AG_DRID1, V_AG_LD_GPR1),
      cmp_sr4_me_drid1 (cmp_sr4_me_drid1_out, SIB_I_ID, ME_DRID1, V_ME_LD_GPR1),
      cmp_sr4_ex_drid1 (cmp_sr4_ex_drid1_out, SIB_I_ID, EX_DRID1, V_EX_LD_GPR1),
      cmp_sr4_ag_drid2 (cmp_sr4_ag_drid2_out, SIB_I_ID, AG_DRID2, V_AG_LD_GPR2),
      cmp_sr4_me_drid2 (cmp_sr4_me_drid2_out, SIB_I_ID, ME_DRID2, V_ME_LD_GPR2),
      cmp_sr4_ex_drid2 (cmp_sr4_ex_drid2_out, SIB_I_ID, EX_DRID2, V_EX_LD_GPR2),

   and2$
      and_sr1_needed (and_sr1_needed_out, SR1_NEEDED, cmp_sr1_ag_drid1_out, cmp_sr1_me_drid1_out, cmp_sr1_ex_drid1_out),
      and_sr1_needed2 (and_sr1_needed_out2, SR1_NEEDED, cmp_sr1_ag_drid2_out, cmp_sr1_me_drid2_out, cmp_sr1_ex_drid2_out);
*/
endmodule
 
