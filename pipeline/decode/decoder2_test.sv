module disp_selector_props (
    input clk, reset, 
    input [127:0] IR,
    input [2:0] disp_sel,
    input disp_size,
    input [31:0] disp
);

logic [7:0]byte3 = IR[111:104];
logic [7:0]byte4 = IR[103:96];
logic [7:0]byte5 = IR[95:88];
logic [7:0]byte6 = IR[87:80];
logic [7:0]byte7 = IR[79:72];
logic [7:0]byte8 = IR[71:64];
logic [7:0]byte9 = IR[63:56];
logic [7:0]byte10 = IR[55:48];
logic [7:0]byte11 = IR[47:40];

logic [31:0] mux1 = {byte6, byte5, byte4, byte3};
logic [31:0] mux2 = {byte7, byte6, byte5, byte4};
logic [31:0] mux3 = {byte8, byte7, byte6, byte5};
logic [31:0] mux4 = {byte9, byte8, byte7, byte6};
logic [31:0] mux5 = {byte10, byte9, byte8, byte7};
logic [31:0] mux6 = {byte11, byte10, byte9, byte8};

logic [31:0] smux1 = $signed(byte3);
logic [31:0] smux2 = $signed(byte4);
logic [31:0] smux3 = $signed(byte5);
logic [31:0] smux4 = $signed(byte6);
logic [31:0] smux5 = $signed(byte7);
logic [31:0] smux6 = $signed(byte8);

assert property (@(posedge clk) (disp_sel==3'b010) && (disp_size==0) |-> (disp==mux1));
assert property (@(posedge clk) (disp_sel==3'b011) && (disp_size==0) |-> (disp==mux2));
assert property (@(posedge clk) (disp_sel==3'b100) && (disp_size==0) |-> (disp==mux3));
assert property (@(posedge clk) (disp_sel==3'b101) && (disp_size==0) |-> (disp==mux4));
assert property (@(posedge clk) (disp_sel==3'b110) && (disp_size==0) |-> (disp==mux5));
assert property (@(posedge clk) (disp_sel==3'b111) && (disp_size==0) |-> (disp==mux6));

assert property (@(posedge clk) (disp_sel==3'b010) && (disp_size==1) |-> (disp==smux1));
assert property (@(posedge clk) (disp_sel==3'b011) && (disp_size==1) |-> (disp==smux2));
assert property (@(posedge clk) (disp_sel==3'b100) && (disp_size==1) |-> (disp==smux3));
assert property (@(posedge clk) (disp_sel==3'b101) && (disp_size==1) |-> (disp==smux4));
assert property (@(posedge clk) (disp_sel==3'b110) && (disp_size==1) |-> (disp==smux5));
assert property (@(posedge clk) (disp_sel==3'b111) && (disp_size==1) |-> (disp==smux6));


endmodule


module imm_selector_props (
    input clk, reset,
    input [127:0] IR,
    input [15:0] opcode,
    input [3:0] imm_sel,
    input [1:0] imm_size,
    input [31:0] imm
);

logic [7:0]byte1 = IR[127:120];
logic [7:0]byte2 = IR[119:112];
logic [7:0]byte3 = IR[111:104];
logic [7:0]byte4 = IR[103:96];
logic [7:0]byte5 = IR[95:88];
logic [7:0]byte6 = IR[87:80];
logic [7:0]byte7 = IR[79:72];
logic [7:0]byte8 = IR[71:64];
logic [7:0]byte9 = IR[63:56];
logic [7:0]byte10 = IR[55:48];
logic [7:0]byte11 = IR[47:40];
logic [7:0]byte12 = IR[39:32];
logic [7:0]byte13 = IR[31:24];
logic [7:0]byte14 = IR[23:16];
logic [7:0]byte15 = IR[15:8];
logic [7:0]byte16 = IR[7:0];

logic [31:0] mux1 = {byte5, byte4, byte3, byte2};
logic [31:0] mux2 = {byte6, byte5, byte4, byte3};
logic [31:0] mux3 = {byte7, byte6, byte5, byte4};
logic [31:0] mux4 = {byte8, byte7, byte6, byte5};
logic [31:0] mux5 = {byte9, byte8, byte7, byte6};
logic [31:0] mux6 = {byte10, byte9, byte8, byte7};
logic [31:0] mux7 = {byte11, byte10, byte9, byte8};
logic [31:0] mux8 = {byte12, byte11, byte10, byte9};
logic [31:0] mux9 = {byte13, byte12, byte11, byte10};
logic [31:0] mux10 = {byte14, byte13, byte12, byte11};
logic [31:0] mux11 = {byte15, byte14, byte13, byte12};

logic [31:0] smux1 = $signed(byte2);
logic [31:0] smux2 = $signed(byte3);
logic [31:0] smux3 = $signed(byte4);
logic [31:0] smux4 = $signed(byte5);
logic [31:0] smux5 = $signed(byte6);
logic [31:0] smux6 = $signed(byte7);
logic [31:0] smux7 = $signed(byte8);
logic [31:0] smux8 = $signed(byte9);
logic [31:0] smux9 = $signed(byte10);
logic [31:0] smux10 = $signed(byte11);
logic [31:0] smux11 = $signed(byte12);

// Sign extension for opcodes jas only imm_size 8
assume property (@(posedge clk) (opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A) |-> opcode[15:8]==8'h0);
assume property (@(posedge clk) (opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A) |-> imm_size==0);

assert property (@(posedge clk) (imm_sel==4'b0001) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux1[7:0]));
assert property (@(posedge clk) (imm_sel==4'b0010) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux2[7:0]));
assert property (@(posedge clk) (imm_sel==4'b0011) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux3[7:0]));
assert property (@(posedge clk) (imm_sel==4'b0100) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux4[7:0]));
assert property (@(posedge clk) (imm_sel==4'b0101) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux5[7:0]));
assert property (@(posedge clk) (imm_sel==4'b0110) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux6[7:0]));
assert property (@(posedge clk) (imm_sel==4'b0111) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux7[7:0]));
assert property (@(posedge clk) (imm_sel==4'b1000) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux8[7:0]));
assert property (@(posedge clk) (imm_sel==4'b1001) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux9[7:0]));
assert property (@(posedge clk) (imm_sel==4'b1010) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux10[7:0]));
assert property (@(posedge clk) (imm_sel==4'b1011) && (imm_size==0) && !((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==mux11[7:0]));

assert property (@(posedge clk) (imm_sel==4'b0001) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux1));
assert property (@(posedge clk) (imm_sel==4'b0010) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux2));
assert property (@(posedge clk) (imm_sel==4'b0011) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux3));
assert property (@(posedge clk) (imm_sel==4'b0100) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux4));
assert property (@(posedge clk) (imm_sel==4'b0101) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux5));
assert property (@(posedge clk) (imm_sel==4'b0110) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux6));
assert property (@(posedge clk) (imm_sel==4'b0111) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux7));
assert property (@(posedge clk) (imm_sel==4'b1000) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux8));
assert property (@(posedge clk) (imm_sel==4'b1001) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux9));
assert property (@(posedge clk) (imm_sel==4'b1010) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux10));
assert property (@(posedge clk) (imm_sel==4'b1011) && (imm_size==0) && ((opcode[7:0]==8'h83) || (opcode[7:0]==8'h6A)) |-> (imm==smux11));


// No case where we have immediate starts from 12th byte and imm_size is 16
//assert property (@(posedge clk) (imm_sel==4'b1011) && (imm_size==1) |-> (imm==mux11[15:0]));
assert property (@(posedge clk) (imm_sel==4'b0001) && (imm_size==1) |-> (imm==mux1[15:0]));
assert property (@(posedge clk) (imm_sel==4'b0010) && (imm_size==1) |-> (imm==mux2[15:0]));
assert property (@(posedge clk) (imm_sel==4'b0011) && (imm_size==1) |-> (imm==mux3[15:0]));
assert property (@(posedge clk) (imm_sel==4'b0100) && (imm_size==1) |-> (imm==mux4[15:0]));
assert property (@(posedge clk) (imm_sel==4'b0101) && (imm_size==1) |-> (imm==mux5[15:0]));
assert property (@(posedge clk) (imm_sel==4'b0110) && (imm_size==1) |-> (imm==mux6[15:0]));
assert property (@(posedge clk) (imm_sel==4'b0111) && (imm_size==1) |-> (imm==mux7[15:0]));
assert property (@(posedge clk) (imm_sel==4'b1000) && (imm_size==1) |-> (imm==mux8[15:0]));
assert property (@(posedge clk) (imm_sel==4'b1001) && (imm_size==1) |-> (imm==mux9[15:0]));
assert property (@(posedge clk) (imm_sel==4'b1010) && (imm_size==1) |-> (imm==mux10[15:0]));

// No case where we have immediate starts from 12th byte and imm_size is 32
//assert property (@(posedge clk) (imm_sel==4'b1011) && (imm_size==2) |-> (imm==mux11[31:0]));
assert property (@(posedge clk) (imm_sel==4'b0001) && (imm_size==2) |-> (imm==mux1[31:0]));
assert property (@(posedge clk) (imm_sel==4'b0010) && (imm_size==2) |-> (imm==mux2[31:0]));
assert property (@(posedge clk) (imm_sel==4'b0011) && (imm_size==2) |-> (imm==mux3[31:0]));
assert property (@(posedge clk) (imm_sel==4'b0100) && (imm_size==2) |-> (imm==mux4[31:0]));
assert property (@(posedge clk) (imm_sel==4'b0101) && (imm_size==2) |-> (imm==mux5[31:0]));
assert property (@(posedge clk) (imm_sel==4'b0110) && (imm_size==2) |-> (imm==mux6[31:0]));
assert property (@(posedge clk) (imm_sel==4'b0111) && (imm_size==2) |-> (imm==mux7[31:0]));
assert property (@(posedge clk) (imm_sel==4'b1000) && (imm_size==2) |-> (imm==mux8[31:0]));
assert property (@(posedge clk) (imm_sel==4'b1001) && (imm_size==2) |-> (imm==mux9[31:0]));
assert property (@(posedge clk) (imm_sel==4'b1010) && (imm_size==2) |-> (imm==mux10[31:0]));

endmodule

module offset_selector_props (
    input clk, reset, 
    input [127:0] IR,
    input [2:0] off_sel,
    input [1:0] offset_size,
    input [47:0] offset
);

logic [7:0]byte1 = IR[127:120];
logic [7:0]byte2 = IR[119:112];
logic [7:0]byte3 = IR[111:104];
logic [7:0]byte4 = IR[103:96];
logic [7:0]byte5 = IR[95:88];
logic [7:0]byte6 = IR[87:80];
logic [7:0]byte7 = IR[79:72];
logic [7:0]byte8 = IR[71:64];
logic [7:0]byte9 = IR[63:56];
logic [7:0]byte10 = IR[55:48];
logic [7:0]byte11 = IR[47:40];
logic [7:0]byte12 = IR[39:32];
logic [7:0]byte13 = IR[31:24];
logic [7:0]byte14 = IR[23:16];
logic [7:0]byte15 = IR[15:8];
logic [7:0]byte16 = IR[7:0];

logic [47:0] mux1 = {byte7, byte6, byte5, byte4, byte3, byte2};
logic [47:0] mux2 = {byte8, byte7, byte6, byte5, byte4, byte3};
logic [47:0] mux3 = {byte9, byte8, byte7, byte6, byte5, byte4};
logic [47:0] mux4 = {byte10, byte9, byte8, byte7, byte6, byte5};
logic [47:0] mux5 = {byte11, byte10, byte9, byte8, byte7, byte6};

assert property (@(posedge clk) (off_sel==3'b001) && (offset_size==0) |-> (offset=={40'b0, mux5[7:0]}));
assert property (@(posedge clk) (off_sel==3'b100) && (offset_size==0) |-> (offset=={40'b0, mux4[7:0]}));
assert property (@(posedge clk) (off_sel==3'b101) && (offset_size==0) |-> (offset=={40'b0, mux1[7:0]}));
assert property (@(posedge clk) (off_sel==3'b110) && (offset_size==0) |-> (offset=={40'b0, mux2[7:0]}));
assert property (@(posedge clk) (off_sel==3'b111) && (offset_size==0) |-> (offset=={40'b0, mux3[7:0]}));

assert property (@(posedge clk) (off_sel==3'b001) && (offset_size==1) |-> (offset==mux5[15:0]));
assert property (@(posedge clk) (off_sel==3'b100) && (offset_size==1) |-> (offset==mux4[15:0]));
assert property (@(posedge clk) (off_sel==3'b101) && (offset_size==1) |-> (offset==mux1[15:0]));
assert property (@(posedge clk) (off_sel==3'b110) && (offset_size==1) |-> (offset==mux2[15:0]));
assert property (@(posedge clk) (off_sel==3'b111) && (offset_size==1) |-> (offset==mux3[15:0]));

assert property (@(posedge clk) (off_sel==3'b001) && (offset_size==2) |-> (offset==mux5[31:0]));
assert property (@(posedge clk) (off_sel==3'b100) && (offset_size==2) |-> (offset==mux4[31:0]));
assert property (@(posedge clk) (off_sel==3'b101) && (offset_size==2) |-> (offset==mux1[31:0]));
assert property (@(posedge clk) (off_sel==3'b110) && (offset_size==2) |-> (offset==mux2[31:0]));
assert property (@(posedge clk) (off_sel==3'b111) && (offset_size==2) |-> (offset==mux3[31:0]));

assert property (@(posedge clk) (off_sel==3'b001) && (offset_size==3) |-> (offset==mux5[47:0]));
assert property (@(posedge clk) (off_sel==3'b100) && (offset_size==3) |-> (offset==mux4[47:0]));
assert property (@(posedge clk) (off_sel==3'b101) && (offset_size==3) |-> (offset==mux1[47:0]));
assert property (@(posedge clk) (off_sel==3'b110) && (offset_size==3) |-> (offset==mux2[47:0]));
assert property (@(posedge clk) (off_sel==3'b111) && (offset_size==3) |-> (offset==mux3[47:0]));

endmodule

module comp16_props (
    input clk, reset, 
    input [15:0] in0, in1,
    input out, out_bar
);

assert property (@(posedge clk) (in0==in1) |-> (out==1));
assert property (@(posedge clk) (in0==in1) |-> (out_bar==0));
assert property (@(posedge clk) (in0!=in1) |-> (out==0));
assert property (@(posedge clk) (in0!=in1) |-> (out_bar==1));


endmodule


//bind decode_stage2 disp_selector_props wrp_disp_selector (
//    .clk(clk),
//    .reset(reset),
//    .IR(u_disp_selector.IR),
//    .disp_sel(u_disp_selector.disp_sel),
//    .disp_size(u_disp_selector.disp_size),
//    .disp(u_disp_selector.disp)
//);

//bind decode_stage2 imm_selector_props wrp_imm_selector (
//    .clk(clk),
//    .reset(reset),
//    .opcode(u_imm_selector.opcode),
//    .IR(IR),
//    .imm_sel(u_imm_selector.imm_sel),
//    .imm_size(u_imm_selector.imm_size),
//    .imm(u_imm_selector.imm)
//);

//bind decode_stage2 offset_selector_props wrp_offset_selector (
//    .clk(clk),
//    .reset(reset),
//    .IR(IR),
//    .off_sel(u_offset_selector.off_sel),
//    .offset_size(u_offset_selector.offset_size),
//    .offset(u_offset_selector.offset)
//);

bind decode_stage2 comp16_props wrp_comp16 (
    .clk(clk),
    .reset(reset),
    .out(comp_0F7F.out),
    .out_bar(comp_0F7F.out_bar),
    .in0(comp_0F7F.in0),
    .in1(comp_0F7F.in1)
);
