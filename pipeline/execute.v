// Control store width needs to be adjusted

module execute (
   input CLK, SET, RST,

   input V,
   input [31:0] NEIP,
   input [15:0] NCS,
   input [63:0] CONTROL_STORE,

   input [31:0] A, B,
   input [63:0] MM_A, MM_B,
   input [31:0] SP_XCHG_DATA,

   input [31:0] MEM_WR_ADDR,
   input [1:0] DATA_SIZE,

   input [2:0] DE_ALUK_EX,
   input [2:0] DRID1, DRID2,

   input D2_MEM_WR_WB, D2_LD_GPR1_WB, D2_LD_MM_WB,
   input DF_FLAG,

   output [31:0] NEIP_OUT,
   output [15:0] NCS_OUT,
   output [63:0] CONTROL_STORE_OUT,

   output [31:0] SR1_DATA_OUT,
   output [31:0] ALU_RESULT_OUT,
   output [63:0] MM_RESULT_OUT,
   output [31:0] SP_XCHG_DATA_OUT,

   output [31:0] MEM_WR_ADDR_OUT,
   output [1:0] DATA_SIZE_OUT,

   output [2:0] DE_ALUK_EX_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output D2_MEM_WR_WB_OUT, D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT
);
`include "../control_store/control_store_wires.v"
`include "../control_store/control_store_signals.v"

   wire [2:0] mux_sz_pos_out, mux_sz_neg_out;
   wire [31:0] mux_sz_out, add_sz_out;

   wire [31:0] temp_reg_out, mux_b_out;

   wire [2:0] mux_pop_sz_out;
   wire [31:0] mux_pop_out, add_pop_out;

   wire [31:0] u_alu32_out, u_shf_out;

   mux2$ mux_neip [31:0] (NEIP_OUT, NEIP, A, CS_MUX_NEXT_EIP_EX);
   mux2$ mux_ncs [15:0] (NCS_OUT, NCS, A[15:0], CS_MUX_NEXT_CSEG_EX);

   assign CONTROL_STORE_OUT = CONTROL_STORE;

   mux4$
      mux_sz_pos [2:0] (mux_sz_pos_out, 3'b001, 3'b010, 3'b100, , DATA_SIZE[0], DATA_SIZE[1]),
      mux_sz_neg [2:0] (mux_sz_neg_out, 3'b111, 3'b110, 3'b100, , DATA_SIZE[0], DATA_SIZE[1]);
   mux2$ mux_sz [31:0] (mux_sz_out, {29'b0, mux_sz_pos_out}, {29'b1, mux_sz_neg_out}, DF_FLAG);
   adder32 add_sz (add_sz_out, , B, mux_sz_out, 1'b0);
   mux2$ mux_sr1_data [31:0] (SR1_DATA_OUT, SP_XCHG_DATA, add_sz_out, CS_MUX_SR1_DATA_EX);

// module reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);
   reg32e$ temp (CLK, A, temp_reg_out, , 1'b1, 1'b1, CS_LD_TEMP_EX);
   mux2$ mux_b [31:0] (mux_b_out, B, temp_reg_out, CS_MUX_B_EX);

   alu32 u_alu32 (.A(A), .B(mux_b_out), .sel(DE_ALUK_EX), .OUT(u_alu32_out));
   shf32 u_shf32 (.A(A), .AMT(B[4:0]), .DIR(DE_ALUK_EX[2]), .OUT(u_shf_out));

   mux2$ mux_result [31:0] (ALU_RESULT_OUT, u_alu32_out, u_shf_out, CS_MUX_RESULT_EX);

   alu64 u_alu64 (.A(MM_A), .B(MM_B), .sel(DE_ALUK_EX), .OUT(MM_RESULT_OUT));

   mux2$
      mux_pop_sz [2:0] (mux_pop_sz_out, 3'b010, 3'b100, DATA_SIZE[1]),
      mux_pop [31:0] (mux_pop_out, 32'b0, {29'b0, mux_pop_sz_out}, CS_MUX_SP_POP_EX);
   adder32 add_pop (add_pop_out, , SP_XCHG_DATA, mux_pop_out, 1'b0);

   mux2$ mux_sp_xchg [31:0] (SP_XCHG_DATA_OUT, add_pop_out, A, CS_MUX_SP_XCHG_DATA_EX);

   assign MEM_WR_ADDR_OUT = MEM_WR_ADDR;
   assign DATA_SIZE_OUT = DATA_SIZE;

   assign DE_ALUK_EX_OUT = DE_ALUK_EX;
   assign DRID1_OUT = DRID1;
   assign DRID2_OUT = DRID2;

   assign D2_MEM_WR_WB_OUT = D2_MEM_WR_WB;
   assign D2_LD_GPR1_WB_OUT = D2_LD_GPR1_WB;
   assign D2_LD_MM_WB_OUT = D2_LD_MM_WB;

endmodule
