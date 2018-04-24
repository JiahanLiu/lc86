module reg_scoreboard_check (
   input V,
   input REG_NEEDED,

   input [2:0] REG,
   input [7:0] REG_SCOREBOARD,

   output STALL
);

   wire mux0_out;
   wire sb7, sb6, sb5, sb4, sb3, sb2, sb1, sb0;
   wire and0_out;

   assign {sb7, sb6, sb5, sb4, sb3, sb2, sb1, sb0} = REG_SCOREBOARD;
   mux8 mux0 (mux0_out, sb0, sb1, sb2, sb3, sb4, sb5, sb6, sb7, REG);

   and3$ and0 (and0_out, V, REG_NEEDED, mux0_out);
   assign STALL = and0_out;

endmodule

module gpr_scoreboard_check (
   input V,
   input REG_NEEDED,

   input [2:0] REG,
   input [1:0] SIZE,

   input [23:0] GPR_SCOREBOARD,

   output STALL
);

   wire [3:0] sb7, sb6, sb5, sb4, sb3, sb2, sb1, sb0;
   wire [3:0] mux0_out;

   assign {sb7[2:0], sb6[2:0], sb5[2:0], sb4[2:0], sb3[2:0], sb2[2:0], sb1[2:0], sb0[2:0]} = GPR_SCOREBOARD;

   wire or0_out, or1_out, or2_out, and0_out, and1_out;
   wire mux1_out;
   wire [2:0] reg_sel;

   // reg_sel[2] = REG[2] & (SIZE[1] | SIZE[0])
   // if SIZE 8-bits, only get ID3 to ID0
   or2$ or0 (or0_out, SIZE[1], SIZE[0]);
   and2$ and0 (and0_out, REG[2], or0_out);
   assign reg_sel[2] = and0_out;
   assign reg_sel[1:0] = REG[1:0];
   
   mux8_4 mux0 (mux0_out, sb0, sb1, sb2, sb3, sb4, sb5, sb6, sb7, reg_sel);

   // if SIZE 8-bits, look at low 8 or high 8 based on REG[2]
   mux2$ mux1 (mux1_out, mux0_out[0], mux0_out[1], REG[2]);

   // if SIZE 16-bits, of the low 16-bits, stall if either byte is set
   or2$ or1 (or1_out, mux0_out[1], mux0_out[0]);

   // if SIZE 32-bits, stall if any scoreboard bit is set
   or3$ or2 (or2_out, mux0_out[2], mux0_out[1], mux0_out[0]);

   // if SIZE 64-bits, no gprs need to be checked
   mux4$ mux2 (mux2_out, mux1_out, or1_out, or2_out, 1'b0, SIZE[0], SIZE[1]);

   // STALL = if stage is Valid && REG_NEEDED && scoreboard bit is high
   and3$ and1 (and1_out, mux2_out, V, REG_NEEDED);
   assign STALL = and1_out;

endmodule

