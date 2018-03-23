module ucontrol_store (
    input [7:0] opcode,
    input opcode_size,
    output [63:0] control_signal
);

wire [63:0] cs1, cs2, cs3, cs4, cs5, cs6, cs7, cs8;
wire [63:0] out1m, out2m;
wire opcode5_buf, opcode6_buf, opcode7_buf;
wire [4:0] opcode_buf;

bufferH16$ buf1[4:0] (opcode_buf, opcode[4:0]);
bufferH64$ buf2 (opcode5_buf, opcode[5]);
bufferH64$ buf3 (opcode6_buf, opcode[6]);
bufferH16$ buf4 (opcode7_buf, opcode[6]);

rom64b32w$ u_rom1 (.A(opcode_buf[4:0]), .OE(1'b1), .DOUT(cs1) );
rom64b32w$ u_rom2 (.A(opcode_buf[4:0]), .OE(1'b1), .DOUT(cs2) );
rom64b32w$ u_rom3 (.A(opcode_buf[4:0]), .OE(1'b1), .DOUT(cs3) );
rom64b32w$ u_rom4 (.A(opcode_buf[4:0]), .OE(1'b1), .DOUT(cs4) );
rom64b32w$ u_rom5 (.A(opcode_buf[4:0]), .OE(1'b1), .DOUT(cs5) );
rom64b32w$ u_rom6 (.A(opcode_buf[4:0]), .OE(1'b1), .DOUT(cs6) );
rom64b32w$ u_rom7 (.A(opcode_buf[4:0]), .OE(1'b1), .DOUT(cs7) );
rom64b32w$ u_rom8 (.A(opcode_buf[4:0]), .OE(1'b1), .DOUT(cs8) );

mux4_16$ mux1[3:0] (out1m, cs1, cs2, cs3, cs4, opcode5_buf, opcode6_buf);
mux4_16$ mux2[3:0] (out2m, cs5, cs6, cs7, cs8, opcode5_buf, opcode6_buf);

mux2_16$ mux3[3:0] (control_signal, out1m, out2m, opcode7_buf);

endmodule
