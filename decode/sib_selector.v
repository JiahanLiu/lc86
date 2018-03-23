// Input is IR[55:16]

module sib_selector (
    input [39:0] instr_buf,
    input [2:0] sib_sel,
    output [7:0] sib
);

wire [7:0] byte7, byte3, byte4, byte5, byte6;
wire sib_sel0, sib_sel1, sib_sel2;
wire [7:0] out1m;

assign byte7 = instr_buf[39:32];
assign byte6 = instr_buf[31:24];
assign byte5 = instr_buf[23:16];
assign byte4 = instr_buf[15:8];
assign byte3 = instr_buf[7:0];

bufferH16$ buf1 (sib_sel0, sib_sel[0]);
bufferH16$ buf2 (sib_sel1, sib_sel[1]);
bufferH16$ buf3 (sib_sel2, sib_sel[2]);

mux4_8$ mux1 (out1m, byte6, byte3, byte4, byte5, sib_sel0, sib_sel1);
mux2_8$ mux2 (sib, byte7, out1m, sib_sel2);

endmodule
