// Input is IR[47:8]

module modrm_selector (
    input [39:0] instr_buf,
    input [2:0] modrm_sel,
    output [7:0] modrm
);

wire [7:0] byte2, byte3, byte4, byte5, byte6;
wire [7:0] out1m;
wire modrm_sel0, modrm_sel1, modrm_sel2;

assign byte2 = instr_buf[39:32];
assign byte3 = instr_buf[31:24];
assign byte4 = instr_buf[23:16];
assign byte5 = instr_buf[15:8];
assign byte6 = instr_buf[7:0];

bufferH16$ buf1 (modrm_sel0, modrm_sel[0]);
bufferH16$ buf2 (modrm_sel1, modrm_sel[1]);
bufferH16$ buf3 (modrm_sel2, modrm_sel[2]);

mux4_8$ mux1 (out1m, byte5, byte2, byte3, byte4, modrm_sel0, modrm_sel1);
mux2_8$ mux2 (modrm, byte6, out1m, modrm_sel2);

endmodule
