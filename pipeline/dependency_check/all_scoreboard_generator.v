module all_scoreboard_generator (
   input V,

   input [2:0] DR1, DR2, DR3,
   input [1:0] DR1_SIZE, DR2_SIZE, DR3_SIZE,

   input LD_GPR1, LD_GPR2, LD_GPR3,
   input LD_SEG, LD_CSEG,
   input LD_MM,

   output [23:0] GPR_SCOREBOARD,
   output [7:0] SEG_SCOREBOARD,
   output [7:0] MM_SCOREBOARD
);

   wire [7:0] and0_out, and1_out, or0_out;
   wire [7:0] and2_out;

   wire [7:0] seg_scoreboard, cseg_scoreboard, mm_scoreboard;

   reg_scoreboard_generator
      u_reg_scoreboard_generator_seg (DR1, seg_scoreboard, ),
      u_reg_scoreboard_generator_cseg (3'b001, cseg_scoreboard, ),
      u_reg_scoreboard_generator_mm (DR1, mm_scoreboard, );

   and3$
      and0 [7:0] (and0_out, seg_scoreboard, V, LD_SEG),
      and1 [7:0] (and1_out, cseg_scoreboard, V, LD_CSEG);
   or2$ or0 [7:0] (or0_out, and0_out, and1_out);
   assign SEG_SCOREBOARD = or0_out;

   and3$ and2 [7:0] (and2_out, mm_scoreboard, V, LD_MM);
   assign MM_SCOREBOARD = and2_out;

   wire [2:0] dr1_bar, dr2_bar, dr3_bar;
   wire [1:0] dr1_size_bar, dr2_size_bar, dr3_size_bar;

   wire [23:0] gpr1_scoreboard, gpr2_scoreboard, gpr3_scoreboard;

   inv1$
      inv0 [2:0] (dr1_bar, DR1),
      inv1 [2:0] (dr2_bar, DR2),
      inv2 [2:0] (dr3_bar, DR3),
      inv3 [1:0] (dr1_size_bar, DR1_SIZE),
      inv4 [1:0] (dr2_size_bar, DR2_SIZE),
      inv5 [1:0] (dr3_size_bar, DR3_SIZE);

   gpr_scoreboard_generator
      u_gpr_scoreboard_generator_gpr1 (DR1, dr1_bar, DR1_SIZE, dr1_size_bar, gpr1_scoreboard),
      u_gpr_scoreboard_generator_gpr2 (DR2, dr2_bar, DR2_SIZE, dr2_size_bar, gpr2_scoreboard),
      u_gpr_scoreboard_generator_gpr3 (DR3, dr3_bar, DR3_SIZE, dr3_size_bar, gpr3_scoreboard);

   wire [23:0] and3_out, and4_out, and5_out;
   wire [23:0] or1_out;

   and3$
      and3 [23:0] (and3_out, gpr1_scoreboard, V, LD_GPR1),
      and4 [23:0] (and4_out, gpr2_scoreboard, V, LD_GPR2),
      and5 [23:0] (and5_out, gpr3_scoreboard, V, LD_GPR3);
   or3$ or1 [23:0] (or1_out, and3_out, and4_out, and5_out);
   assign GPR_SCOREBOARD = or1_out;

endmodule

