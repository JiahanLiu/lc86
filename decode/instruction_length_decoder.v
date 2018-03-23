module instruction_length_decoder (
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
    output [2:0] disp_sel,
    output [3:0] imm_sel,
    output [3:0] read_ptr_update
);

wire imm_size1_b, imm_size0_b, off_size1_b, off_size0_b;
wire opcode_size_b, disp_size_b;
wire [2:0] imm_l;
wire off_l0, prefix_l1, prefix_l0, disp_l2, disp_l0;
wire [3:0] opcode_lp, prefix_lp, disp_lp, imm_lp, offset_lp, modrm_lp, sib_lp;
wire [3:0] out1c, out2c, out3c, out4c, out5c;

inv1$ inv1 (imm_size1_b, imm_size[1]);
inv1$ inv2 (imm_size0_b, imm_size[0]);
inv1$ inv3 (off_size1_b, offset_size[1]);
inv1$ inv4 (off_size0_b, offset_size[1]);

// Logic for imm_length
// imm_l2 = (imm_size1 &!imm_size0);
// imm_l1 = (!imm_size1 &imm_size0);
// imm_l0 = (!imm_size1 &!imm_size0);
and3$ and1 (imm_l[2], imm_size[1], imm_size0_b, imm_present);
and3$ and2 (imm_l[1], imm_size1_b, imm_size[0], imm_present);
and3$ and3 (imm_l[0], imm_size1_b, imm_size0_b, imm_present);

// Logic for offset_length
// off_l2 = (off_size1);
// off_l1 = (off_size0);
// off_l0 = (!off_size1 &!off_size0);
and3$ and4 (off_l0, off_size1_b, off_size0_b, offset_present);

// Logic for disp_length
// disp_l2 = (!disp_size);
// disp_l1 = 0;
// disp_l0 = (disp_size);

// Logic for opcode length
// opcode_l1 = opcode_size
// opcode_l0 = !opcode_size
inv1$ inv_op (opcode_size_b, opcode_size);
assign opcode_lp = {1'b0, 1'b0, opcode_size, opcode_size_b};

and2$ and5 (prefix_l1, prefix_present, prefix_size[1]);
and2$ and6 (prefix_l0, prefix_present, prefix_size[0]);
assign prefix_lp = {1'b0, 1'b0, prefix_l1, prefix_l0};

inv1$ inv_disp (disp_size_b, disp_size);
and2$ and7 (disp_l2, disp_present, disp_size_b);
and2$ and8 (disp_l0, disp_present, disp_size);
assign disp_lp = {1'b0, disp_l2, 1'b0, disp_l0};

assign imm_lp = {1'b0, imm_l[2], imm_l[1], imm_l[0]};
assign offset_lp = {1'b0, offset_size[1], offset_size[0], off_l0};
assign modrm_lp = {1'b0, 1'b0, 1'b0, modrm_present};
assign sib_lp = {1'b0, 1'b0, 1'b0, sib_present};

carry_lookahead cl1 (out1c, , , ,modrm_lp, sib_lp, 1'b0);
carry_lookahead cl2 (out2c, , , ,prefix_lp, opcode_lp, 1'b0);
carry_lookahead cl3 (out3c, , , ,disp_lp, imm_lp, 1'b0);

carry_lookahead cl4 (out4c, , , ,out1c, out2c, 1'b0);
carry_lookahead cl5 (out5c, , , ,out3c, offset_lp, 1'b0);
carry_lookahead cl6 (read_ptr_update, , , ,out4c, out5c, 1'b0);

carry_lookahead cl7 (imm_sel, , , ,out4c, disp_lp, 1'b0);
assign disp_sel = out4c[2:0];

endmodule
