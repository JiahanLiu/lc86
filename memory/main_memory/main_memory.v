module main_memory (
    input CLK,
    input [14:0] ADDR,
    input CE, WR,
    input [1:0] WRITE_SIZE,
    input [1:0] SRC,
    input [31:0] DATA_IN,
    output [31:0] DATA_OUT
);

// 4 buffers for what?
wire [127:0] BUF_ICACHE, BUF_DCACHE;
wire [127:0] data_blk1, data_blk2, buf_out;
assign OE = ADDR[14];

inv1$ inv1 (ADDR14_B, ADDR[14]);

tristate16L$ tri1_buf1 (.enbar(ADDR[14]), .in(DATA_IN[15:0]), .out(data_blk2[15:0]));
tristate16L$ tri1_buf2 (.enbar(ADDR[14]), .in(DATA_IN[31:16]), .out(data_blk2[31:16]));
//tristate16L$ tri1_buf3 (.enbar(ADDR[14]), .in(DATA_IN[47:32]), .out(data_blk2[47:32]));
//tristate16L$ tri1_buf4 (.enbar(ADDR[14]), .in(DATA_IN[63:48]), .out(data_blk2[63:48]));
//tristate16L$ tri1_buf5 (.enbar(ADDR[14]), .in(DATA_IN[79:64]), .out(data_blk2[79:64]));
//tristate16L$ tri1_buf6 (.enbar(ADDR[14]), .in(DATA_IN[95:80]), .out(data_blk2[95:80]));
//tristate16L$ tri1_buf7 (.enbar(ADDR[14]), .in(DATA_IN[111:96]), .out(data_blk2[111:96]));
//tristate16L$ tri1_buf8 (.enbar(ADDR[14]), .in(DATA_IN[127:112]), .out(data_blk2[127:112]));

tristate16L$ tri2_buf1 (.enbar(ADDR14_B), .in(DATA_IN[15:0]), .out(data_blk1[15:0]));
tristate16L$ tri2_buf2 (.enbar(ADDR14_B), .in(DATA_IN[31:16]), .out(data_blk1[31:16]));
//tristate16L$ tri2_buf3 (.enbar(ADDR14_B), .in(DATA_IN[47:32]), .out(data_blk1[47:32]));
//tristate16L$ tri2_buf4 (.enbar(ADDR14_B), .in(DATA_IN[63:48]), .out(data_blk1[63:48]));
//tristate16L$ tri2_buf5 (.enbar(ADDR14_B), .in(DATA_IN[79:64]), .out(data_blk1[79:64]));
//tristate16L$ tri2_buf6 (.enbar(ADDR14_B), .in(DATA_IN[95:80]), .out(data_blk1[95:80]));
//tristate16L$ tri2_buf7 (.enbar(ADDR14_B), .in(DATA_IN[111:96]), .out(data_blk1[111:96]));
//tristate16L$ tri2_buf8 (.enbar(ADDR14_B), .in(DATA_IN[127:112]), .out(data_blk1[127:112]));

word_lines block1 (ADDR[13:7], data_blk1, OE, WR, CE);
word_lines block2 (ADDR[13:7], data_blk2, OE, WR, CE);

mux32_2way mux1 (buf_out[31:0], data_blk1[31:0], data_blk2[31:0], ADDR[14]);
mux32_2way mux2 (buf_out[63:32], data_blk1[63:32], data_blk2[63:32], ADDR[14]);
mux32_2way mux3 (buf_out[95:64], data_blk1[95:64], data_blk2[95:64], ADDR[14]);
mux32_2way mux4 (buf_out[127:96], data_blk1[127:96], data_blk2[127:96], ADDR[14]);

//reg32e$ 

endmodule


module word_lines (
    input [6:0] A,
    input [127:0] DIO,
    input OE,
    input [15:0] WR, 
    input CE
);

sram128x8$ sram0 (A, DIO[7:0], OE, WR[0], CE);
sram128x8$ sram1 (A, DIO[15:8], OE, WR[1], CE);
sram128x8$ sram2 (A, DIO[23:16], OE, WR[2], CE);
sram128x8$ sram3 (A, DIO[31:24], OE, WR[3], CE);
sram128x8$ sram4 (A, DIO[39:32], OE, WR[4], CE);
sram128x8$ sram5 (A, DIO[47:40], OE, WR[5], CE);
sram128x8$ sram6 (A, DIO[55:48], OE, WR[6], CE);
sram128x8$ sram7 (A, DIO[63:56], OE, WR[7], CE);
sram128x8$ sram8 (A, DIO[71:64], OE, WR[8], CE);
sram128x8$ sram9 (A, DIO[79:72], OE, WR[9], CE);
sram128x8$ sram10 (A, DIO[87:80], OE, WR[10], CE);
sram128x8$ sram11 (A, DIO[95:88], OE, WR[11], CE);
sram128x8$ sram12 (A, DIO[103:96], OE, WR[12], CE);
sram128x8$ sram13 (A, DIO[111:104], OE, WR[13], CE);
sram128x8$ sram14 (A, DIO[119:112], OE, WR[14], CE);
sram128x8$ sram15 (A, DIO[127:120], OE, WR[15], CE);

endmodule
