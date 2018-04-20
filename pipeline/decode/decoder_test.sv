//

module prefix_decoder_props(
    input clk,
    input reset, 
    input isPrefix1, isPrefix2, isPrefix3,
    input seg1, seg2, seg3,
    input prefix_present,
    input [1:0] prefix_length,
    input [1:0] segID_sel
);

assume property (@(posedge clk) !(seg1 && seg2));
assume property (@(posedge clk) !(seg3 && seg2));
assume property (@(posedge clk) !(seg1 && seg3));
assume property (@(posedge clk) (!isPrefix1 |-> !seg1));
assume property (@(posedge clk) (!isPrefix2 |-> !seg2));
assume property (@(posedge clk) (!isPrefix3 |-> !seg3));
assume property (@(posedge clk) isPrefix3 |-> (isPrefix2 && isPrefix1));
assume property (@(posedge clk) isPrefix2 |-> isPrefix1);

assert property (@(posedge clk) disable iff(reset) !isPrefix1 |-> !prefix_present);
assert property (@(posedge clk) disable iff(reset) !isPrefix1 |-> (prefix_length == 0));
assert property (@(posedge clk) disable iff(reset) (isPrefix1 | isPrefix2 | isPrefix3) |-> prefix_present);
assert property (@(posedge clk) disable iff(reset) (isPrefix1 && !isPrefix2) |-> (prefix_length == 1));
assert property (@(posedge clk) disable iff(reset) (isPrefix1 && isPrefix2 && !isPrefix3) |-> (prefix_length == 2));
assert property (@(posedge clk) disable iff(reset) (isPrefix1 && isPrefix2 && isPrefix3) |-> (prefix_length == 3));
assert property (@(posedge clk) seg1 |-> (segID_sel == 0));
assert property (@(posedge clk) seg2 |-> (segID_sel == 1));
assert property (@(posedge clk) seg3 |-> (segID_sel == 2));

endmodule

module prefix_checker_props(
    input clk,
    input reset, 
    input [7:0] instr_byte,
    input isPrefix,
    input isOpcode,
    input operand_override,
    input segment_override,
    input repeat_prefix,
    input [2:0] segID
);

sequence prefix_check(sig1);
    (sig1 == 8'hF2) || (sig1 == 8'h2E) || (sig1 == 8'h36) || (sig1 == 8'h3E) || (sig1 == 8'h26) 
    || (sig1 == 8'h64) || (sig1 == 8'h65) || (sig1 == 8'h66);
endsequence

sequence opcode_check(sig1);
    !((sig1 == 8'hF2) || (sig1 == 8'h2E) || (sig1 == 8'h36) || (sig1 == 8'h3E) || (sig1 == 8'h26) 
    || (sig1 == 8'h64) || (sig1 == 8'h65) || (sig1 == 8'h66));
endsequence

sequence segment_r(sig1);
    (sig1 == 8'h36) || (sig1 == 8'h2E) || (sig1 == 8'h3E) || (sig1 == 8'h26) 
    || (sig1 == 8'h64) || (sig1 == 8'h65);
endsequence

assert property (@(posedge clk) prefix_check(instr_byte) |-> isPrefix);
assert property (@(posedge clk) opcode_check(instr_byte) |-> isOpcode );
assert property (@(posedge clk) segment_r(instr_byte) |-> segment_override);
assert property (@(posedge clk) (instr_byte == 8'h66) |-> operand_override);
assert property (@(posedge clk) (instr_byte == 8'hF2) |-> repeat_prefix);
assert property (@(posedge clk) (instr_byte == 8'h2E) |-> (segID == 1));
assert property (@(posedge clk) (instr_byte == 8'h36) |-> (segID == 2));
assert property (@(posedge clk) (instr_byte == 8'h3E) |-> (segID == 3));
assert property (@(posedge clk) (instr_byte == 8'h26) |-> (segID == 0));
assert property (@(posedge clk) (instr_byte == 8'h64) |-> (segID == 4));
assert property (@(posedge clk) (instr_byte == 8'h65) |-> (segID == 5));

endmodule


module opcode_length_decoder_props (
    input clk, reset,
    input isOpcode1, isOpcode2, isOpcode3, isOpcode4, isOpcode5,
    input [7:0] byte1, byte2, byte3, byte4, byte5,
    input [2:0] opcode_sel,
    input opcode_size
);

assume property (@(posedge clk) isOpcode1 && (byte1==8'h0F) |-> isOpcode2);
assume property (@(posedge clk) !isOpcode1 && isOpcode2 && (byte2 == 8'h0F) |-> isOpcode3);
assume property (@(posedge clk) !isOpcode1 && !isOpcode2 && isOpcode3 && (byte3 == 8'h0F) |-> isOpcode4);
assume property (@(posedge clk) !isOpcode1 && !isOpcode2 && !isOpcode3 && isOpcode4 && (byte4 == 8'h0F) |-> isOpcode5 );

assume property (@(posedge clk) !((byte1 == 8'h0F) && (byte2 == 8'h0F)));
assume property (@(posedge clk) !((byte1 == 8'h0F) && (byte3 == 8'h0F)));
assume property (@(posedge clk) !((byte1 == 8'h0F) && (byte4 == 8'h0F)));
assume property (@(posedge clk) !((byte1 == 8'h0F) && (byte5 == 8'h0F)));
assume property (@(posedge clk) !((byte2 == 8'h0F) && (byte3 == 8'h0F)));
assume property (@(posedge clk) !((byte2 == 8'h0F) && (byte4 == 8'h0F)));
assume property (@(posedge clk) !((byte2 == 8'h0F) && (byte5 == 8'h0F)));
assume property (@(posedge clk) !((byte3 == 8'h0F) && (byte4 == 8'h0F)));
assume property (@(posedge clk) !((byte3 == 8'h0F) && (byte5 == 8'h0F)));
assume property (@(posedge clk) !((byte4 == 8'h0F) && (byte5 == 8'h0F)));


assert property (@(posedge clk) isOpcode1 && !(byte1 == 8'h0F) |-> (opcode_sel == 0));
assert property (@(posedge clk) !isOpcode1 && isOpcode2 && !(byte2 == 8'h0F) |-> (opcode_sel == 1));
assert property (@(posedge clk) !isOpcode1 && !isOpcode2 && isOpcode3 && !(byte3 == 8'h0F) |-> (opcode_sel == 2));
assert property (@(posedge clk) !isOpcode1 && !isOpcode2 && !isOpcode3 && isOpcode4 && !(byte4 == 8'h0F) |-> (opcode_sel == 3));

assert property (@(posedge clk) isOpcode1 && (byte1 == 8'h0F) && isOpcode2 |-> (opcode_sel == 4));
assert property (@(posedge clk) !isOpcode1 && isOpcode2 && (byte2 == 8'h0F) && isOpcode3 |-> (opcode_sel == 5));
assert property (@(posedge clk) !isOpcode1 && !isOpcode2 && isOpcode3 && (byte3 == 8'h0F) && isOpcode4 |-> (opcode_sel == 6));
assert property (@(posedge clk) !isOpcode1 && !isOpcode2 && !isOpcode3 && isOpcode4 && (byte4 == 8'h0F) && isOpcode5 |-> (opcode_sel == 7));

endmodule 


module modrm_detector_props (
    input clk, reset, 
    input [15:0] opcode,
    input modrm_present
);

sequence modrm_p();
    (opcode==16'h0081) || (opcode==16'h0083) || (opcode==16'h0001) || (opcode==16'h0000) || (opcode==16'h0002) || 
    (opcode==16'h0003) || (opcode==16'h0008) || (opcode==16'h0009) || (opcode==16'h000A) || (opcode==16'h000B) || 
    (opcode==16'h0F42) || (opcode==16'h0F6F) || (opcode==16'h0F70) || (opcode==16'h0F7F) || (opcode==16'h0FB0) ||
    (opcode==16'h0FB1) || (opcode==16'h0FED) || (opcode==16'h0FFD) || (opcode==16'h0FFE) || (opcode==16'h0020) ||
    (opcode==16'h0021) || (opcode==16'h0022) || (opcode==16'h0023) || (opcode==16'h0080) || (opcode==16'h0086) ||
    (opcode==16'h0087) || (opcode==16'h0088) || (opcode==16'h0089) || (opcode==16'h008A) || (opcode==16'h008B) ||
    (opcode==16'h008C) || (opcode==16'h008E) || (opcode==16'h008F) || (opcode==16'h00C0) || (opcode==16'h00C1) ||
    (opcode==16'h00C6) || (opcode==16'h00C7) || (opcode==16'h00D0) || (opcode==16'h00D1) || (opcode==16'h00D1) ||
    (opcode==16'h00D2) || (opcode==16'h00D3) || (opcode==16'h00F6) || (opcode==16'h00F7) || (opcode==16'h00FE) ||
    (opcode==16'h00FF);
endsequence

sequence modrm_np();
    !((opcode==16'h0081) || (opcode==16'h0083) || (opcode==16'h0001) || (opcode==16'h0000) || (opcode==16'h0002) || 
    (opcode==16'h0003) || (opcode==16'h0008) || (opcode==16'h0009) || (opcode==16'h000A) || (opcode==16'h000B) || 
    (opcode==16'h0F42) || (opcode==16'h0F6F) || (opcode==16'h0F70) || (opcode==16'h0F7F) || (opcode==16'h0FB0) ||
    (opcode==16'h0FB1) || (opcode==16'h0FED) || (opcode==16'h0FFD) || (opcode==16'h0FFE) || (opcode==16'h0020) ||
    (opcode==16'h0021) || (opcode==16'h0022) || (opcode==16'h0023) || (opcode==16'h0080) || (opcode==16'h0086) ||
    (opcode==16'h0087) || (opcode==16'h0088) || (opcode==16'h0089) || (opcode==16'h008A) || (opcode==16'h008B) ||
    (opcode==16'h008C) || (opcode==16'h008E) || (opcode==16'h008F) || (opcode==16'h00C0) || (opcode==16'h00C1) ||
    (opcode==16'h00C6) || (opcode==16'h00C7) || (opcode==16'h00D0) || (opcode==16'h00D1) || (opcode==16'h00D1) ||
    (opcode==16'h00D2) || (opcode==16'h00D3) || (opcode==16'h00F6) || (opcode==16'h00F7) || (opcode==16'h00FE) ||
    (opcode==16'h00FF));
endsequence


assert property (@(posedge clk) modrm_p |-> modrm_present);
assert property (@(posedge clk) modrm_np |-> !modrm_present);

endmodule 


module immediate_detector_props (
    input clk, reset,
    input [15:0] opcode,
    input operand_override,
    input imm_present,
    input [1:0] imm_size
);

sequence imm_size8();
    (opcode==16'h04) || (opcode==16'h0C) || (opcode==16'h0F70) || (opcode==16'h24) || (opcode==16'h6A) || 
    (opcode==16'h80) || (opcode==16'h83) || (opcode==16'hB0) || (opcode==16'hB1) || (opcode==16'hB2) ||
    (opcode==16'hB3) || (opcode==16'hB4) || (opcode==16'hB5) || (opcode==16'hB6) || (opcode==16'hB7) ||
    (opcode==16'hC0) || (opcode==16'hC1) || (opcode==16'hC6);
endsequence

sequence imm_size16();
    (opcode==16'hC2) || (opcode==16'hCA) || 
    (operand_override && ((opcode==16'h68) || (opcode==16'h05) || (opcode==16'h0D) || (opcode==16'h25) || 
    (opcode==16'h81) || (opcode==16'hB8) || (opcode==16'hB9) || (opcode==16'hBA) || (opcode==16'hBB) ||
    (opcode==16'hBC) || (opcode==16'hBD) || (opcode==16'hBE) || (opcode==16'hBF) || (opcode==16'hC7)));
endsequence

sequence imm_size32();
    !operand_override && ((opcode==16'h68) || (opcode==16'h05) || (opcode==16'h0D) || (opcode==16'h25) || 
    (opcode==16'h81) || (opcode==16'hB8) || (opcode==16'hB9) || (opcode==16'hBA) || (opcode==16'hBB) ||
    (opcode==16'hBC) || (opcode==16'hBD) || (opcode==16'hBE) || (opcode==16'hBF) || (opcode==16'hC7));
endsequence

sequence imm_np();
    !((opcode==16'h04) || (opcode==16'h0C) || (opcode==16'h0F70) || (opcode==16'h24) || (opcode==16'h6A) || 
    (opcode==16'h80) || (opcode==16'h83) || (opcode==16'hB0) || (opcode==16'hB1) || (opcode==16'hB2) ||
    (opcode==16'hB3) || (opcode==16'hB4) || (opcode==16'hB5) || (opcode==16'hB6) || (opcode==16'hB7) ||
    (opcode==16'hC0) || (opcode==16'hC1) || (opcode==16'hC6) || (opcode==16'hC2) || (opcode==16'hCA) || 
    (opcode==16'h68) || (opcode==16'h05) || (opcode==16'h0D) || (opcode==16'h25) || 
    (opcode==16'h81) || (opcode==16'hB8) || (opcode==16'hB9) || (opcode==16'hBA) || (opcode==16'hBB) ||
    (opcode==16'hBC) || (opcode==16'hBD) || (opcode==16'hBE) || (opcode==16'hBF) || (opcode==16'hC7));
endsequence

assert property (@(posedge clk) imm_size8 |-> imm_present && (imm_size==0));
assert property (@(posedge clk) imm_size16 |-> imm_present && (imm_size==1));
assert property (@(posedge clk) imm_size32 |-> imm_present && (imm_size==2));
assert property (@(posedge clk) imm_np |-> !imm_present);

endmodule


module sib_disp_detector_props (
    input [7:0] modrm,
    input disp_present, 
    input disp_size,
    input modrm_present,
    input sib_present,
    input clk, reset
);

sequence sib_p();
    modrm_present && (((modrm[7:6]==2'b00) || (modrm[7:6]==2'b01) || (modrm[7:6]==2'b10)) && (modrm[2:0]==3'b100));
endsequence

sequence disp_p();
    modrm_present && ((modrm[7:6]==2'b01) || (modrm[7:6]==2'b10) || ((modrm[7:6]==2'b00) && (modrm[2:0]==3'b101)));
endsequence

sequence sib_np();
    !(((modrm[7:6]==2'b00) || (modrm[7:6]==2'b01) || (modrm[7:6]==2'b10)) && (modrm[2:0]==3'b100));
endsequence

sequence disp_np();
    !((modrm[7:6]==2'b01) || (modrm[7:6]==2'b10) || ((modrm[7:6]==2'b00) && (modrm[2:0]==3'b101)));
endsequence

assert property (@(posedge clk) sib_p |-> sib_present);
assert property (@(posedge clk) sib_np |-> !sib_present);
assert property (@(posedge clk) disp_p |-> disp_present);
assert property (@(posedge clk) disp_np |-> !disp_present);
assert property (@(posedge clk) (modrm[7:6]==2'b01) |-> disp_size);
assert property (@(posedge clk) ((modrm[7:6]==2'b10) || ((modrm[7:6]==2'b00) && (modrm[2:0]==3'b101))) |-> !disp_size);

endmodule


module offset_detector_props (
    input clk, reset, 
    input operand_override,
    input [15:0] opcode,
    input opcode_size,
    input offset_present,
    input [1:0] offset_size
);

assume property (@(posedge clk) (opcode[15:8]==8'h00) || (opcode[15:8]==8'h0F));
assume property (@(posedge clk) opcode_size |-> (opcode[15:8]==8'h0F));
assume property (@(posedge clk) !opcode_size |-> (opcode[15:8]==8'h00));

assert property (@(posedge clk) (opcode[7:0]==8'h9A) && !opcode_size |-> offset_present && offset_size==3);

assert property (@(posedge clk) (opcode_size && operand_override && ((opcode[7:0]==8'h87) || (opcode[7:0]==8'h85))) |-> offset_present && (offset_size==1));
assert property (@(posedge clk) (!opcode_size && operand_override && ((opcode[7:0]==8'hE8) || (opcode[7:0]==8'hE9))) |-> offset_present && (offset_size==1));

assert property (@(posedge clk) (!opcode_size && operand_override && (opcode[7:0]==8'hEA)) |-> offset_present && offset_size==2);
assert property (@(posedge clk) (!opcode_size && !operand_override && (opcode[7:0]==8'hEA)) |-> offset_present && offset_size==3);

assert property (@(posedge clk) (opcode_size && !operand_override && ((opcode[7:0]==8'h87) || (opcode[7:0]==8'h85))) |-> offset_present && (offset_size==2));
assert property (@(posedge clk) (!opcode_size && !operand_override && ((opcode[7:0]==8'hE8) || (opcode[7:0]==8'hE9))) |-> offset_present && (offset_size==2));
assert property (@(posedge clk) !opcode_size && ((opcode[7:0]==8'hEB) || (opcode[7:0]==8'h77) || (opcode[7:0]==8'h75)) |-> offset_present && (offset_size==0));

endmodule


module modrm_pointer_props (
    input clk, reset, 
    input opcode_size,
    input prefix_present, 
    input [1:0] prefix_size,
    input [2:0] modrm_sel
);

assert property (@(posedge clk) !prefix_present && !opcode_size |-> (modrm_sel==5));
assert property (@(posedge clk) !prefix_present && opcode_size |-> (modrm_sel==6));
assert property (@(posedge clk) !opcode_size && prefix_present && (prefix_size==1) |-> (modrm_sel==6));
assert property (@(posedge clk) !opcode_size && prefix_present && (prefix_size==2) |-> (modrm_sel==7));
assert property (@(posedge clk) !opcode_size && prefix_present && (prefix_size==3) |-> (modrm_sel==4));
assert property (@(posedge clk) opcode_size && prefix_present && (prefix_size==1) |-> (modrm_sel==7));
assert property (@(posedge clk) opcode_size && prefix_present && (prefix_size==2) |-> (modrm_sel==4));
assert property (@(posedge clk) opcode_size && prefix_present && (prefix_size==3) |-> (modrm_sel==1));

endmodule

module modrm_selector_props (
    input clk, reset,
    input [39:0] instr_buf,
    input [2:0] modrm_sel,
    input [7:0] modrm
);

assert property (@(posedge clk) (modrm_sel==5) |-> (modrm==instr_buf[39:32]));
assert property (@(posedge clk) (modrm_sel==6) |-> (modrm==instr_buf[31:24]));
assert property (@(posedge clk) (modrm_sel==7) |-> (modrm==instr_buf[23:16]));
assert property (@(posedge clk) (modrm_sel==4) |-> (modrm==instr_buf[15:8]));
assert property (@(posedge clk) (modrm_sel==1) |-> (modrm==instr_buf[7:0]));

endmodule

module sib_selector_props (
    input clk, reset,
    input [39:0] instr_buf,
    input [2:0] sib_sel,
    input [7:0] sib
);

assert property (@(posedge clk) (sib_sel==5) |-> (sib==instr_buf[39:32]));
assert property (@(posedge clk) (sib_sel==6) |-> (sib==instr_buf[31:24]));
assert property (@(posedge clk) (sib_sel==7) |-> (sib==instr_buf[23:16]));
assert property (@(posedge clk) (sib_sel==4) |-> (sib==instr_buf[15:8]));
assert property (@(posedge clk) (sib_sel==1) |-> (sib==instr_buf[7:0]));

endmodule


module instruction_length_decoder_props (
    input clk, reset,
    input prefix_present,
    input [1:0] prefix_size,
    input opcode_size, 
    input modrm_present,
    input sib_present, 
    input offset_present,
    input [1:0] offset_size, 
    input disp_present, 
    input disp_size,
    input imm_present,
    input [1:0] imm_size,
    input [2:0] disp_sel,
    input [3:0] imm_sel,
    input [3:0] read_ptr_update,
    input [3:0] out1c, out2c, out3c, out4c, out5c
);

reg [3:0] off_s, imm_s, disp_s;
reg [3:0] off_val, imm_val, disp_val;
reg [3:0] off_sh, imm_sh, disp_sh;
reg [3:0] off_p, imm_p, disp_p, disp_sel_val;
reg [1:0] prefix_p;
reg off_or, imm_or, disp_or;

assign off_s = offset_size;
assign disp_s = disp_size;
assign imm_s = imm_size;

assign off_or = off_s[1] |off_s[0];
assign off_sh = {off_or, off_or, off_or, off_or};
assign off_p = {offset_present, offset_present, offset_present, offset_present};
assign off_val = off_p & (!(off_s[1] | off_s[0]) + (off_sh & (off_s << 1)));

assign imm_or = imm_s[1] | imm_s[0];
assign imm_sh = {imm_or, imm_or, imm_or, imm_or};
assign imm_p = {imm_present, imm_present, imm_present, imm_present};
assign imm_val = imm_p & (!(imm_s[1] | imm_s[0]) + (imm_sh & (imm_s << 1)));

assign disp_sh = {!disp_size, !disp_size, !disp_size, !disp_size};
assign disp_p = {disp_present, disp_present, disp_present, disp_present};
assign disp_val = disp_p & (disp_size + (disp_sh & (!disp_s << 2)));

assign prefix_p = {prefix_present, prefix_present};
assign disp_sel_val = modrm_present+sib_present + (prefix_p & prefix_size) + (opcode_size+1);

sequence length_update();
    read_ptr_update==((prefix_p & prefix_size) + (opcode_size+1) + modrm_present + sib_present + off_val + disp_val + imm_val);
endsequence

assume property (@(posedge clk) imm_size<=2);
assert property (@(posedge clk) out1c==(modrm_present+sib_present));
assert property (@(posedge clk) out2c==((prefix_p & prefix_size) + (opcode_size+1)));
assert property (@(posedge clk) out3c==(disp_val+imm_val));
assert property (@(posedge clk) out4c==(modrm_present+sib_present + (prefix_p & prefix_size) + (opcode_size+1)));
assert property (@(posedge clk) out5c==(disp_val+imm_val+off_val));
assert property (@(posedge clk) length_update());
assert property (@(posedge clk) imm_sel==(modrm_present+sib_present + disp_val + (prefix_p & prefix_size) + (opcode_size+1)));
assert property (@(posedge clk) disp_sel==disp_sel_val[2:0]);

endmodule


module decode_stage1_props (
    input clk, reset, 
    input [127:0] IR, 
    input [3:0] instr_length_updt,
    input [15:0] opcode, 
    input [1:0] prefix_size,
    input prefix_present, segment_override, operand_override, repeat_prefix, 
    input modrm_present, imm_present,
    input [1:0] imm_size,
    input sib_present, disp_present, disp_size,
    input [3:0] imm_sel,
    input [2:0] disp_sel,
    input offset_present,
    input opcode_size, 
    input [1:0] offset_size,
    input [2:0] segID,
    input [7:0] modrm, sib,
    input [2:0] modrm_sel
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

reg [3:0] instr_length = 0;
logic [1:0] prefix_p = {prefix_present, prefix_present};
logic [3:0] disp_sel_val = modrm_present + sib_present + (prefix_p & prefix_size) + (opcode_size+1);

reg [3:0] off_s, imm_s, disp_s;
reg [3:0] off_val, imm_val, disp_val;
reg [3:0] off_sh, imm_sh, disp_sh;
reg [3:0] off_p, imm_p, disp_p, disp_sel_val;
reg [1:0] prefix_p;
reg off_or, imm_or, disp_or;

assign off_s = offset_size;
assign disp_s = disp_size;
assign imm_s = imm_size;

assign off_or = off_s[1] |off_s[0];
assign off_sh = {off_or, off_or, off_or, off_or};
assign off_p = {offset_present, offset_present, offset_present, offset_present};
assign off_val = off_p & (!(off_s[1] | off_s[0]) + (off_sh & (off_s << 1)));

assign imm_or = imm_s[1] | imm_s[0];
assign imm_sh = {imm_or, imm_or, imm_or, imm_or};
assign imm_p = {imm_present, imm_present, imm_present, imm_present};
assign imm_val = imm_p & (!(imm_s[1] | imm_s[0]) + (imm_sh & (imm_s << 1)));

assign disp_sh = {!disp_size, !disp_size, !disp_size, !disp_size};
assign disp_p = {disp_present, disp_present, disp_present, disp_present};
assign disp_val = disp_p & (disp_size + (disp_sh & (!disp_s << 2)));

sequence length_update();
    instr_length_updt==((prefix_p & prefix_size) + (opcode_size+1) + modrm_present + sib_present + off_val + disp_val + imm_val);
endsequence


// Assume that prefix bytes are different
// Assume that prefix has only one segment override
assume property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && !isPrefix(byte3) |-> (byte1 != byte2));
assume property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) |-> (byte1 != byte2) && (byte1!=byte2) && (byte2!=byte3));
assume property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && !isPrefix(byte3) && segment_ovr(byte1) |-> !segment_ovr(byte2));
assume property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && !isPrefix(byte3) && segment_ovr(byte2) |-> !segment_ovr(byte1));
assume property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && segment_ovr(byte1)|-> !segment_ovr(byte2) && !segment_ovr(byte3));
assume property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && segment_ovr(byte2)|-> !segment_ovr(byte1) && !segment_ovr(byte3));
assume property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && segment_ovr(byte3)|-> !segment_ovr(byte1) && !segment_ovr(byte2));

// Opcode assume properties, no opcode 0F0F
// 0F means the next byte is opcode
assume property (@(posedge clk) isOpcode(byte1) && (byte1==8'h0F) |-> isOpcode(byte2));
assume property (@(posedge clk) !isOpcode(byte1) && isOpcode(byte2) && (byte2 == 8'h0F) |-> isOpcode(byte3));
assume property (@(posedge clk) !isOpcode(byte1) && !isOpcode(byte2) && isOpcode(byte3) && (byte3 == 8'h0F) |-> isOpcode(byte4));
assume property (@(posedge clk) !isOpcode(byte1) && !isOpcode(byte2) && !isOpcode(byte3) && isOpcode(byte4) && (byte4 == 8'h0F) |-> isOpcode(byte5) );

assume property (@(posedge clk) !((byte1 == 8'h0F) && (byte2 == 8'h0F)));
assume property (@(posedge clk) !((byte1 == 8'h0F) && (byte3 == 8'h0F)));
assume property (@(posedge clk) !((byte1 == 8'h0F) && (byte4 == 8'h0F)));
assume property (@(posedge clk) !((byte1 == 8'h0F) && (byte5 == 8'h0F)));
assume property (@(posedge clk) !((byte2 == 8'h0F) && (byte3 == 8'h0F)));
assume property (@(posedge clk) !((byte2 == 8'h0F) && (byte4 == 8'h0F)));
assume property (@(posedge clk) !((byte2 == 8'h0F) && (byte5 == 8'h0F)));
assume property (@(posedge clk) !((byte3 == 8'h0F) && (byte4 == 8'h0F)));
assume property (@(posedge clk) !((byte3 == 8'h0F) && (byte5 == 8'h0F)));
assume property (@(posedge clk) !((byte4 == 8'h0F) && (byte5 == 8'h0F)));

// Assume for byte4 is not a prefix if byte1, byte2, byte3 are prefix
assume property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) |-> !isPrefix(byte4));

// Assume immediate size is never 3
assume property (@(posedge clk) imm_size<=2);

// Assume property for opcode
assume property (@(posedge clk) (opcode[15:8]==8'h00) || (opcode[15:8]==8'h0F));
assume property (@(posedge clk) opcode_size |-> (opcode[15:8]==8'h0F));
assume property (@(posedge clk) !opcode_size |-> (opcode[15:8]==8'h00));

function reg isOpcode (reg [7:0] field);
    if((field == 8'hF2) || (field == 8'h2E) || (field == 8'h36) || (field == 8'h3E) || (field == 8'h26) || (field == 8'h64) || (field == 8'h65) || (field == 8'h66)) 
        return 0;
    else 
        return 1;
    isOpcode =1;
endfunction

function reg isPrefix (reg [7:0] field);
    if((field == 8'hF2) || (field == 8'h2E) || (field == 8'h36) || (field == 8'h3E) || (field == 8'h26) || (field == 8'h64) || (field == 8'h65) || (field == 8'h66)) 
        return 1;
    else 
        return 0;
    isPrefix =1;
endfunction

function reg segment_ovr(reg [7:0] sig1);
    if((sig1 == 8'h36) || (sig1 == 8'h2E) || (sig1 == 8'h3E) || (sig1 == 8'h26) || (sig1 == 8'h64) || (sig1 == 8'h65))
        return 1;
    else 
        return 0;
    segment_ovr=1;
endfunction

function reg rep_prefix(reg [7:0] sig1);
    if((sig1 == 8'hF2))
        return 1;
    else 
        return 0;
    rep_prefix=1;
endfunction

function reg oper_ovr(reg [7:0] sig1);
    if((sig1 == 8'h66))
        return 1;
    else 
        return 0;
    oper_ovr=1;
endfunction

function reg sib_p(reg [7:0] sig1);
    if(((sig1[7:6]==2'b00) || (sig1[7:6]==2'b01) || (sig1[7:6]==2'b10)) && (sig1[2:0]==3'b100))
        return 1;
    else
        return 0;
    sib_p=1;
endfunction

function reg disp_pre(reg [7:0] sig1);
    if((sig1[7:6]==2'b01) || (sig1[7:6]==2'b10) || ((sig1[7:6]==2'b00) && (sig1[2:0]==3'b101)))
        return 1;
    else 
        return 0;
    disp_pre=1;
endfunction


function reg modrm_p(reg [15:0] opc);
    if((opc==16'h0081) || (opc==16'h0083) || (opc==16'h0001) || (opc==16'h0000) || (opc==16'h0002) || 
    (opc==16'h0003) || (opc==16'h0008) || (opc==16'h0009) || (opc==16'h000A) || (opc==16'h000B) || 
    (opc==16'h0F42) || (opc==16'h0F6F) || (opc==16'h0F70) || (opc==16'h0F7F) || (opc==16'h0FB0) ||
    (opc==16'h0FB1) || (opc==16'h0FED) || (opc==16'h0FFD) || (opc==16'h0FFE) || (opc==16'h0020) ||
    (opc==16'h0021) || (opc==16'h0022) || (opc==16'h0023) || (opc==16'h0080) || (opc==16'h0086) ||
    (opc==16'h0087) || (opc==16'h0088) || (opc==16'h0089) || (opc==16'h008A) || (opc==16'h008B) ||
    (opc==16'h008C) || (opc==16'h008E) || (opc==16'h008F) || (opc==16'h00C0) || (opc==16'h00C1) ||
    (opc==16'h00C6) || (opc==16'h00C7) || (opc==16'h00D0) || (opc==16'h00D1) || (opc==16'h00D1) ||
    (opc==16'h00D2) || (opc==16'h00D3) || (opc==16'h00F6) || (opc==16'h00F7) || (opc==16'h00FE) ||
    (opc==16'h00FF))
        return 1;
    else 
        return 0;
    modrm_p=1;
endfunction

function reg imm_size8(reg [15:0] opc);
    if((opc==16'h04) || (opc==16'h0C) || (opc==16'h0F70) || (opc==16'h24) || (opc==16'h6A) || 
    (opc==16'h80) || (opc==16'h83) || (opc==16'hB0) || (opc==16'hB1) || (opc==16'hB2) ||
    (opc==16'hB3) || (opc==16'hB4) || (opc==16'hB5) || (opc==16'hB6) || (opc==16'hB7) ||
    (opc==16'hC0) || (opc==16'hC1) || (opc==16'hC6))
        return 1;
    else
        return 0;
    imm_size8=1;
endfunction

function reg imm_size16(reg [15:0] opc);
    if((opc==16'hC2) || (opc==16'hCA) || 
    (operand_override && ((opc==16'h68) || (opc==16'h05) || (opc==16'h0D) || (opc==16'h25) || 
    (opc==16'h81) || (opc==16'hB8) || (opc==16'hB9) || (opc==16'hBA) || (opc==16'hBB) ||
    (opc==16'hBC) || (opc==16'hBD) || (opc==16'hBE) || (opc==16'hBF) || (opc==16'hC7))))
        return 1;
    else
        return 0;
    imm_size16=1;
endfunction

function reg imm_size32(reg [15:0] opc);
    if(!operand_override && ((opc==16'h68) || (opc==16'h05) || (opc==16'h0D) || (opc==16'h25) || 
    (opc==16'h81) || (opc==16'hB8) || (opc==16'hB9) || (opc==16'hBA) || (opc==16'hBB) ||
    (opc==16'hBC) || (opc==16'hBD) || (opc==16'hBE) || (opc==16'hBF) || (opc==16'hC7)))
        return 1;
    else
        return 0;
    imm_size32=1;
endfunction

function reg imm_np(reg [15:0] opc);
    if(!((opc==16'h04) || (opc==16'h0C) || (opc==16'h0F70) || (opc==16'h24) || (opc==16'h6A) || 
    (opc==16'h80) || (opc==16'h83) || (opc==16'hB0) || (opc==16'hB1) || (opc==16'hB2) ||
    (opc==16'hB3) || (opc==16'hB4) || (opc==16'hB5) || (opc==16'hB6) || (opc==16'hB7) ||
    (opc==16'hC0) || (opc==16'hC1) || (opc==16'hC6) || (opc==16'hC2) || (opc==16'hCA) || 
    (opc==16'h68) || (opc==16'h05) || (opc==16'h0D) || (opc==16'h25) || 
    (opc==16'h81) || (opc==16'hB8) || (opc==16'hB9) || (opc==16'hBA) || (opc==16'hBB) ||
    (opc==16'hBC) || (opc==16'hBD) || (opc==16'hBE) || (opc==16'hBF) || (opc==16'hC7)))
        return 1;
    else 
        return 0;
    imm_np=1;
endfunction

// Prefix present
assert property (@(posedge clk) isPrefix(byte1) && !isPrefix(byte2) |-> prefix_present && (prefix_size == 1));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && !isPrefix(byte3) |-> prefix_present && (prefix_size == 2));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) |-> prefix_present && (prefix_size == 3));

// Prefix not present
assert property (@(posedge clk) 
    !((isPrefix(byte1) && !isPrefix(byte2)) || (isPrefix(byte1) && isPrefix(byte2) && !isPrefix(byte3)) || (isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3)))
    |-> !prefix_present);

// Segment override
assert property (@(posedge clk) isPrefix(byte1) && segment_ovr(byte1) |-> segment_override);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && (segment_ovr(byte1) || segment_ovr(byte2)) |-> segment_override);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (segment_ovr(byte1) || segment_ovr(byte2) || segment_ovr(byte3)) |-> segment_override);

// Segment override not present
assert property (@(posedge clk) 
    !((isPrefix(byte1) && !isPrefix(byte2) && segment_ovr(byte1)) || (isPrefix(byte2) && !isPrefix(byte3) && (segment_ovr(byte1) || segment_ovr(byte2)))
    || (isPrefix(byte2) && isPrefix(byte3) && (segment_ovr(byte1) || segment_ovr(byte2) || segment_ovr(byte3)))) |-> !segment_override);


// Repeat prefix present
assert property (@(posedge clk) isPrefix(byte1) && rep_prefix(byte1) |-> repeat_prefix);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && (rep_prefix(byte1) || rep_prefix(byte2)) |-> repeat_prefix);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (rep_prefix(byte1) || rep_prefix(byte2) || rep_prefix(byte3)) |-> repeat_prefix);

// Repeat prefix not present
assert property (@(posedge clk) 
    !((isPrefix(byte1) && !isPrefix(byte2) && rep_prefix(byte1)) || (isPrefix(byte2) && !isPrefix(byte3) && (rep_prefix(byte1) || rep_prefix(byte2)))
    || (isPrefix(byte2) && isPrefix(byte3) && (rep_prefix(byte1) || rep_prefix(byte2) || rep_prefix(byte3)))) |-> !repeat_prefix);

// Operand override prefix present
assert property (@(posedge clk) isPrefix(byte1) && oper_ovr(byte1) |-> operand_override);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && (oper_ovr(byte1) || oper_ovr(byte2)) |-> operand_override);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (oper_ovr(byte1) || oper_ovr(byte2) || oper_ovr(byte3)) |-> operand_override);

// Operand override prefix not present
assert property (@(posedge clk) 
    !((isPrefix(byte1) && !isPrefix(byte2) && oper_ovr(byte1)) || (isPrefix(byte2) && !isPrefix(byte3) && (oper_ovr(byte1) || oper_ovr(byte2)))
    || (isPrefix(byte2) && isPrefix(byte3) && (oper_ovr(byte1) || oper_ovr(byte2) || oper_ovr(byte3)))) |-> !operand_override);

// Opcode and opcode_size
assert property (@(posedge clk) !isPrefix(byte1) && (byte1!=8'h0F) |-> (opcode==byte1) && !opcode_size);
assert property (@(posedge clk) !isPrefix(byte1) && (byte1==8'h0F) |-> (opcode=={byte1, byte2}) && opcode_size);
assert property (@(posedge clk) isPrefix(byte1) && !isPrefix(byte2) && (byte2!=8'h0F) |-> (opcode==byte2) && !opcode_size);
assert property (@(posedge clk) isPrefix(byte1) && !isPrefix(byte2) && (byte2==8'h0F) |-> (opcode=={byte2, byte3}) && opcode_size);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && !isPrefix(byte3) && (byte3!=8'h0F) |-> (opcode==byte3) && !opcode_size);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && !isPrefix(byte3) && (byte3==8'h0F) |-> (opcode=={byte3, byte4}) && opcode_size);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (byte4!=8'h0F) |-> (opcode==byte4) && !opcode_size);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (byte4==8'h0F) |-> (opcode=={byte4, byte5}) && opcode_size);

// Modrm present and modrm
assert property (@(posedge clk) (opcode=={8'b0, byte1}) && modrm_p({8'b0, byte1}) |-> modrm_present && (modrm==byte2));
assert property (@(posedge clk) (opcode=={byte1, byte2}) && (byte1==8'h0F) && modrm_p({byte1, byte2}) |-> modrm_present && (modrm==byte3));
assert property (@(posedge clk) isPrefix(byte1) && (opcode=={8'b0, byte2}) && modrm_p({8'b0, byte2}) |-> modrm_present && (modrm==byte3));
assert property (@(posedge clk) isPrefix(byte1) && (opcode=={byte2, byte3}) && (byte2==8'h0F) && modrm_p({byte2, byte3}) |-> modrm_present && (modrm==byte4));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && (opcode=={8'b0, byte3}) && modrm_p({8'b0, byte3}) |-> modrm_present && (modrm==byte4));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && (opcode=={byte3, byte4}) && (byte3==8'h0F) && modrm_p({byte3, byte4}) |-> modrm_present && (modrm==byte5));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (opcode=={8'b0, byte4}) && modrm_p({8'b0, byte4}) |-> modrm_present && (modrm==byte5));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (opcode=={byte4, byte5}) && (byte4==8'h0F) && modrm_p({byte4, byte5}) |-> modrm_present && (modrm==byte6));

// Modrm sel 
assert property (@(posedge clk) !prefix_present && !opcode_size |-> (modrm_sel==5));
assert property (@(posedge clk) !prefix_present && opcode_size |-> (modrm_sel==6));
assert property (@(posedge clk) !opcode_size && prefix_present && (prefix_size==1) |-> (modrm_sel==6));
assert property (@(posedge clk) !opcode_size && prefix_present && (prefix_size==2) |-> (modrm_sel==7));
assert property (@(posedge clk) !opcode_size && prefix_present && (prefix_size==3) |-> (modrm_sel==4));
assert property (@(posedge clk) opcode_size && prefix_present && (prefix_size==1) |-> (modrm_sel==7));
assert property (@(posedge clk) opcode_size && prefix_present && (prefix_size==2) |-> (modrm_sel==4));
assert property (@(posedge clk) opcode_size && prefix_present && (prefix_size==3) |-> (modrm_sel==1));

// Modrm not present
assert property (@(posedge clk) (opcode=={8'b0, byte1}) && !modrm_p({8'b0, byte1}) |-> !modrm_present);
assert property (@(posedge clk) (opcode=={byte1, byte2}) && (byte1==8'h0F) && !modrm_p({byte1, byte2}) |-> !modrm_present);
assert property (@(posedge clk) isPrefix(byte1) && (opcode=={8'b0, byte2}) && !modrm_p({8'b0, byte2}) |-> !modrm_present);
assert property (@(posedge clk) isPrefix(byte1) && (opcode=={byte2, byte3}) && (byte2==8'h0F) && !modrm_p({byte2, byte3}) |-> !modrm_present);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && (opcode=={8'b0, byte3}) && !modrm_p({8'b0, byte3}) |-> !modrm_present);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && (opcode=={byte3, byte4}) && (byte3==8'h0F) && !modrm_p({byte3, byte4}) |-> !modrm_present);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (opcode=={8'b0, byte4}) && !modrm_p({8'b0, byte4}) |-> !modrm_present);
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (opcode=={byte4, byte5}) && (byte4==8'h0F) && !modrm_p({byte4, byte5}) |-> !modrm_present);

// Sib Present and sib
assert property (@(posedge clk) modrm_present && sib_p(modrm) |-> sib_present);
assert property (@(posedge clk) (opcode=={8'b0, byte1}) && (modrm==byte2) && sib_p(modrm) |-> (sib==byte3));
assert property (@(posedge clk) (opcode=={byte1, byte2}) && (byte1==8'h0F) && (modrm==byte3) && sib_p(modrm) |-> (sib==byte4));
assert property (@(posedge clk) isPrefix(byte1) && (opcode=={8'b0, byte2}) && (modrm==byte3) && sib_p(modrm) |-> (sib==byte4));
assert property (@(posedge clk) isPrefix(byte1) && (opcode=={byte2, byte3}) && (byte2==8'h0F) && (modrm==byte4) && sib_p(modrm) |-> (sib==byte5));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && (opcode=={8'b0, byte3}) && (modrm==byte4) && sib_p(modrm) |-> (sib==byte5));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && (opcode=={byte3, byte4}) && (byte3==8'h0F) && (modrm==byte5) && sib_p(modrm) |-> (sib==byte6));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (opcode=={8'b0, byte4}) && (modrm==byte5) && sib_p(modrm) |-> (sib==byte6));
assert property (@(posedge clk) isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (opcode=={byte4, byte5}) && (byte4==8'h0F) && (modrm==byte6) && sib_p(modrm) |-> (sib==byte7));

// Sib not present
assert property (@(posedge clk) modrm_present && !sib_p(modrm) |-> !sib_present);
assert property (@(posedge clk) !modrm_present |-> !sib_present);

// Disp present
assert property (@(posedge clk) modrm_present && disp_pre(modrm) |-> disp_present);

// Disp not present
assert property (@(posedge clk) modrm_present && !disp_pre(modrm) |-> !disp_present);
assert property (@(posedge clk) !modrm_present |-> !disp_present);

// Disp size
assert property (@(posedge clk) (modrm[7:6]==2'b01) |-> disp_size);
assert property (@(posedge clk) ((modrm[7:6]==2'b10) || ((modrm[7:6]==2'b00) && (modrm[2:0]==3'b101))) |-> !disp_size);

// Disp_sel
assert property (@(posedge clk) disp_sel == disp_sel_val[2:0]);

// Imm_present and imm_size
assert property (@(posedge clk) imm_size8(opcode) |-> imm_present && (imm_size==0));
assert property (@(posedge clk) imm_size16(opcode) |-> imm_present && (imm_size==1));
assert property (@(posedge clk) imm_size32(opcode) |-> imm_present && (imm_size==2));
assert property (@(posedge clk) imm_np(opcode) |-> !imm_present);

// Imm sel
assert property (@(posedge clk) imm_sel==(modrm_present+sib_present + disp_val + (prefix_p & prefix_size) + (opcode_size+1)));

// Offset present and offset size
assert property (@(posedge clk) (opcode[7:0]==8'h9A) && !opcode_size |-> offset_present && offset_size==3);

assert property (@(posedge clk) (opcode_size && operand_override && ((opcode[7:0]==8'h87) || (opcode[7:0]==8'h85))) |-> offset_present && (offset_size==1));
assert property (@(posedge clk) (!opcode_size && operand_override && ((opcode[7:0]==8'hE8) || (opcode[7:0]==8'hE9))) |-> offset_present && (offset_size==1));

assert property (@(posedge clk) (!opcode_size && operand_override && (opcode[7:0]==8'hEA)) |-> offset_present && offset_size==2);
assert property (@(posedge clk) (!opcode_size && !operand_override && (opcode[7:0]==8'hEA)) |-> offset_present && offset_size==3);

assert property (@(posedge clk) (opcode_size && !operand_override && ((opcode[7:0]==8'h87) || (opcode[7:0]==8'h85))) |-> offset_present && (offset_size==2));
assert property (@(posedge clk) (!opcode_size && !operand_override && ((opcode[7:0]==8'hE8) || (opcode[7:0]==8'hE9))) |-> offset_present && (offset_size==2));
assert property (@(posedge clk) !opcode_size && ((opcode[7:0]==8'hEB) || (opcode[7:0]==8'h77) || (opcode[7:0]==8'h75)) |-> offset_present && (offset_size==0));

// Update instruction length
assert property (@(posedge clk) length_update());

// segID output
assert property (@(posedge clk) (isPrefix(byte1) && (byte1 == 8'h2E)) || (isPrefix(byte1) && isPrefix(byte2) && (byte1==8'h2E || byte2==8'h2E))
        && (isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (byte1==8'h2E || byte2==8'h2E || byte3==8'h2E))|-> (segID == 1));
assert property (@(posedge clk) (isPrefix(byte1) && (byte1 == 8'h36)) || (isPrefix(byte1) && isPrefix(byte2) && (byte1==8'h36 || byte2==8'h36))
        && (isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (byte1==8'h36 || byte2==8'h36 || byte3==8'h36))|-> (segID == 2));
assert property (@(posedge clk) (isPrefix(byte1) && (byte1 == 8'h3E)) || (isPrefix(byte1) && isPrefix(byte2) && (byte1==8'h3E || byte2==8'h3E))
        && (isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (byte1==8'h3E || byte2==8'h3E || byte3==8'h3E))|-> (segID == 3));
assert property (@(posedge clk) (isPrefix(byte1) && (byte1 == 8'h26)) || (isPrefix(byte1) && isPrefix(byte2) && (byte1==8'h26 || byte2==8'h26))
        && (isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (byte1==8'h26 || byte2==8'h26 || byte3==8'h26))|-> (segID == 0));
assert property (@(posedge clk) (isPrefix(byte1) && (byte1 == 8'h64)) || (isPrefix(byte1) && isPrefix(byte2) && (byte1==8'h64 || byte2==8'h64))
        && (isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (byte1==8'h64 || byte2==8'h64 || byte3==8'h64))|-> (segID == 4));
assert property (@(posedge clk) (isPrefix(byte1) && (byte1 == 8'h65)) || (isPrefix(byte1) && isPrefix(byte2) && (byte1==8'h65 || byte2==8'h65))
        && (isPrefix(byte1) && isPrefix(byte2) && isPrefix(byte3) && (byte1==8'h65 || byte2==8'h65 || byte3==8'h65))|-> (segID == 5));

//assert property (@(posedge clk) IR[127:112] == 16'hF204 |-> prefix_present && (prefix_size==1) && !opcode_size && (opcode==16'h04) && imm_present && (imm_size==2'b00)
//        && !modrm_present && !sib_present && !disp_present && (instr_length_updt==4'b0011) && repeat_prefix && !operand_override && !segment_override && !offset_present
//        && (imm_sel==4'b0010));

endmodule


module Wrapper;

//bind decode_stage1 prefix_decoder_props wrp_prefix_decode (
//    .clk(clk),
//    .reset(reset),
//    .isPrefix1(u_prefix_decoder.isPrefix1),
//    .isPrefix2(u_prefix_decoder.isPrefix2),
//    .isPrefix3(u_prefix_decoder.isPrefix3),
//    .seg1(u_prefix_decoder.isSeg_ovrr1),
//    .seg2(u_prefix_decoder.isSeg_ovrr2),
//    .seg3(u_prefix_decoder.isSeg_ovrr3),
//    .segID_sel(u_prefix_decoder.segID_sel),
//    .prefix_present(u_prefix_decoder.prefix_present),
//    .prefix_length(u_prefix_decoder.prefix_length)
//);
//
//bind decode_stage1 prefix_checker_props wrp_prefix_check (
//    .clk(clk),
//    .reset(reset),
//    .instr_byte(u_prefix_checker1.instr_byte),
//    .isOpcode(u_prefix_checker1.isOpcode),
//    .isPrefix(u_prefix_checker1.isPrefix),
//    .operand_override(u_prefix_checker1.operand_override),
//    .segment_override(u_prefix_checker1.segment_override),
//    .repeat_prefix(u_prefix_checker1.repeat_prefix),
//    .segID(u_prefix_checker1.segID)
//);
//
//bind decode_stage1 opcode_length_decoder_props wrp_opcode_length_decode (
//    .clk(clk),
//    .reset(reset),
//    .isOpcode1(u_opcode_length_decoder.isOpcode1),
//    .isOpcode2(u_opcode_length_decoder.isOpcode2),
//    .isOpcode3(u_opcode_length_decoder.isOpcode3),
//    .isOpcode4(u_opcode_length_decoder.isOpcode4),
//    .isOpcode5(u_opcode_length_decoder.isOpcode5),
//    .byte1(u_opcode_length_decoder.byte1),
//    .byte2(u_opcode_length_decoder.byte2),
//    .byte3(u_opcode_length_decoder.byte3),
//    .byte4(u_opcode_length_decoder.byte4),
//    .byte5(u_opcode_length_decoder.byte5),
//    .opcode_sel(u_opcode_length_decoder.opcode_sel),
//    .opcode_size(u_opcode_length_decoder.opcode_size)
//);
//
//bind decode_stage1 modrm_detector_props wrp_modrm_detector (
//    .clk(clk),
//    .reset(reset),
//    .opcode(u_modrm_detector.opcode),
//    .modrm_present(u_modrm_detector.modrm_present)
//);
//
//bind decode_stage1 immediate_detector_props wrp_immediate_detector (
//    .clk(clk),
//    .reset(reset),
//    .opcode(u_immediate_detector.opcode),
//    .operand_override(u_immediate_detector.operand_override),
//    .imm_present(u_immediate_detector.imm_present),
//    .imm_size(u_immediate_detector.imm_size)
//);
//
//bind decode_stage1 sib_disp_detector_props wrp_sib_disp_detector (
//    .clk(clk),
//    .reset(reset),
//    .modrm(u_sib_disp_detector.modrm),
//    .modrm_present(u_sib_disp_detector.modrm_present),
//    .disp_present(u_sib_disp_detector.disp_present),
//    .sib_present(u_sib_disp_detector.sib_present),
//    .disp_size(u_sib_disp_detector.disp_size)
//);
//
//bind decode_stage1 offset_detector_props wrp_offset_detector (
//    .clk(clk),
//    .reset(reset),
//    .opcode(u_offset_detector.opcode),
//    .operand_override(u_offset_detector.operand_override),
//    .opcode_size(u_offset_detector.opcode_size),
//    .offset_present(u_offset_detector.offset_present),
//    .offset_size(u_offset_detector.offset_size)
//);
//
//bind decode_stage1 modrm_pointer_props wrp_modrm_pointer (
//    .clk(clk),
//    .reset(reset),
//    .opcode_size(u_modrm_pointer.opcode_size),
//    .prefix_present(u_modrm_pointer.prefix_present),
//    .prefix_size(u_modrm_pointer.prefix_size),
//    .modrm_sel(u_modrm_pointer.modrm_sel)
//);
//
//bind decode_stage1 modrm_selector_props wrp_modrm_selector_props (
//    .clk(clk),
//    .reset(reset),
//    .instr_buf(u_modrm_selector.instr_buf),
//    .modrm_sel(u_modrm_selector.modrm_sel),
//    .modrm(u_modrm_selector.modrm)
//);
//
//bind decode_stage1 sib_selector_props wrp_sib_selector_props (
//    .clk(clk),
//    .reset(reset),
//    .instr_buf(u_sib_selector.instr_buf),
//    .sib_sel(u_sib_selector.sib_sel),
//    .sib(u_sib_selector.sib)
//);
//
//bind decode_stage1 instruction_length_decoder_props wrp_instruction_length_decoder (
//    .clk(clk),
//    .reset(reset),
//    .prefix_present(u_instruction_length_decoder.prefix_present),
//    .prefix_size(u_instruction_length_decoder.prefix_size),
//    .opcode_size(u_instruction_length_decoder.opcode_size), 
//    .modrm_present(u_instruction_length_decoder.modrm_present),
//    .sib_present(u_instruction_length_decoder.sib_present), 
//    .offset_present(u_instruction_length_decoder.offset_present),
//    .offset_size(u_instruction_length_decoder.offset_size), 
//    .disp_present(u_instruction_length_decoder.disp_present), 
//    .disp_size(u_instruction_length_decoder.disp_size),
//    .imm_present(u_instruction_length_decoder.imm_present),
//    .imm_size(u_instruction_length_decoder.imm_size),
//    .disp_sel(u_instruction_length_decoder.disp_sel),
//    .imm_sel(u_instruction_length_decoder.imm_sel),
//    .read_ptr_update(u_instruction_length_decoder.read_ptr_update),
//    .out1c(u_instruction_length_decoder.cl1.sum),
//    .out2c(u_instruction_length_decoder.cl2.sum),
//    .out3c(u_instruction_length_decoder.cl3.sum),
//    .out4c(u_instruction_length_decoder.cl4.sum),
//    .out5c(u_instruction_length_decoder.cl5.sum)
//);
//
//bind decode_stage1 decode_stage1_props wrp_decode_stage1 (
//    .clk(clk),
//    .reset(reset), 
//    .IR(IR), 
//    .instr_length_updt(instr_length_updt),
//    .opcode(opcode), 
//    .prefix_size(prefix_size),
//    .prefix_present(prefix_present),
//    .segment_override(segment_override),
//    .operand_override(operand_override),
//    .repeat_prefix(repeat_prefix), 
//    .modrm_present(modrm_present),
//    .imm_present(imm_present),
//    .imm_size(imm_size),
//    .sib_present(sib_present),
//    .disp_present(disp_present),
//    .disp_size(disp_size),
//    .imm_sel(imm_sel),
//    .disp_sel(disp_sel),
//    .offset_present(offset_present),
//    .opcode_size(opcode_size), 
//    .offset_size(offset_size),
//    .segID(segID),
//    .modrm(modrm),
//    .sib(sib),
//    .modrm_sel(modrm_sel)
//);

endmodule
