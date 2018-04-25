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
wire [15:0] write_en_f, write_en1, write_en2, write_en3, write_en4, write_en_read;
wire [15:0] write_en_blk1, write_en_blk2;
wire [31:0] bit_lines;
wire [4:0] row_address;

assign row_address = ADDR[4:0];
assign column_address = ADDR[14:5];

// Size 00 |-> writing one byte
assign write_en_read = 16'hFFFF;
assign write_en1 = 16'hFFFE;
assign write_en2 = 16'hFFFD;
assign write_en3 = 16'hFFFC;
assign write_en4 = 16'hFFFB;

mux4_16$ mux1_WR (write_en_f, write_en1, write_en2, write_en3, write_en4, WRITE_SIZE);
inv1$ inv1 (ADDR14_B, ADDR[14]);

and2$ write_mask[15:0] (write_en_blk1, write_en_f, {16{ADDR14_B}};
and2$ write_mask[15:0] (write_en_blk2, write_en_f, {16{ADDR[14]}};

tristate16L$ tri1_buf1 (.enbar(ADDR[14]), .in(DATA_IN[15:0]), .out(data_blk1[15:0]));
tristate16L$ tri1_buf2 (.enbar(ADDR[14]), .in(DATA_IN[31:16]), .out(data_blk1[31:16]));

tristate16L$ tri2_buf1 (.enbar(ADDR14_B), .in(DATA_IN[15:0]), .out(data_blk2[15:0]));
tristate16L$ tri2_buf2 (.enbar(ADDR14_B), .in(DATA_IN[31:16]), .out(data_blk2[31:16]));

word_lines block1 (ADDR[13:7], data_blk1, 1'b0, write_en_blk1, 1'b0);
word_lines block2 (ADDR[13:7], data_blk2, 1'b0, write_en_blk2, 1'b0);

mux32_2way mux1 (buf_out[31:0], data_blk1[31:0], data_blk2[31:0], ADDR[14]);
mux32_2way mux2 (buf_out[63:32], data_blk1[63:32], data_blk2[63:32], ADDR[14]);
mux32_2way mux3 (buf_out[95:64], data_blk1[95:64], data_blk2[95:64], ADDR[14]);
mux32_2way mux4 (buf_out[127:96], data_blk1[127:96], data_blk2[127:96], ADDR[14]);


decoder5to32 u_column_decoder (bit_lines, row_address);
decoder5to32 u_row_decoder1 (bit_lines, row_address);
decoder5to32 u_row_decoder2 (bit_lines, row_address);


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
