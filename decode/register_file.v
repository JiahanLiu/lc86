// Size of the control signals to be defined - it will be a part of control
// store. WE, data_size, 

module register_file (
    input clk, set, reset,
    input [2:0] SR1, SR2, SR3, SR4,
    input [2:0] DR1, DR2, DR3,
    input write_DR1, write_DR2, write_DR3,
    input [31:0] result1, result2, result3,

    output [31:0] regA, regB, regC, regD
);

wire write_DR1_buf, write_DR2_buf, write_DR3_buf;
wire [7:0] write_en1, write_en2, write_en3;
wire [7:0] write_en1_b, write_en2_b, write_en3_b;
wire [7:0] out1a;
wire [7:0] outw1, outw2, outw3;
wire [31:0] write_data0, write_data1, write_data2, write_data3;
wire [31:0] write_data4, write_data5, write_data6, write_data7;
wire [7:0] r_sel1, r_sel0;
wire r_sel00_buf, r_sel01_buf, r_sel02_buf, r_sel03_buf, r_sel04_buf;
wire r_sel05_buf, r_sel06_buf, r_sel07_buf;
wire r_sel10_buf, r_sel11_buf, r_sel12_buf, r_sel13_buf, r_sel14_buf;
wire r_sel15_buf, r_sel16_buf, r_sel17_buf;
wire [31:0] reg0_out, reg1_out, reg2_out, reg3_out;
wire [31:0] reg4_out, reg5_out, reg6_out, reg7_out;
wire [31:0] out1m, out2m, out3m, out4m, out5m, out6m, out7m, out8m;
wire SR10, SR11, SR12;
wire SR20, SR21, SR22;
wire SR30, SR31, SR32;
wire SR40, SR41, SR42;

bufferH16$ buf1 (write_DR1_buf, write_DR1);
bufferH16$ buf2 (write_DR2_buf, write_DR2);
bufferH16$ buf3 (write_DR3_buf, write_DR3);

decoder3_8$ u_decoder1 (.SEL(DR1), .Y(write_en1), .YBAR() );
decoder3_8$ u_decoder2 (.SEL(DR2), .Y(write_en2), .YBAR() );
decoder3_8$ u_decoder3 (.SEL(DR3), .Y(write_en3), .YBAR() );

and2$ andw1[7:0] (outw1, write_en1, write_DR1_buf);
and2$ andw2[7:0] (outw2, write_en2, write_DR2_buf);
and2$ andw3[7:0] (outw3, write_en3, write_DR3_buf);
or3$ or1[7:0] (out1a, outw1, outw2, outw3);

// Here d1, d2, d3 are write_en1, write_en2, write_en3
// s1 = (!d1 &!d2 &d3);
// s0 = (!d1 &d2 &!d3);

inv1$ inv1[7:0] (write_en1_b, write_en1);
inv1$ inv2[7:0] (write_en2_b, write_en2);
inv1$ inv3[7:0] (write_en3_b, write_en3);

// Write the correct data
and3$ and2[7:0] (r_sel1, write_en1_b, write_en2_b, write_en3);
and3$ and3[7:0] (r_sel0, write_en1_b, write_en2, write_en3_b);

bufferH16$ buf4 (r_sel00_buf, r_sel0[0]);
bufferH16$ buf5 (r_sel01_buf, r_sel0[1]);
bufferH16$ buf6 (r_sel02_buf, r_sel0[2]);
bufferH16$ buf7 (r_sel03_buf, r_sel0[3]);
bufferH16$ buf8 (r_sel04_buf, r_sel0[4]);
bufferH16$ buf9 (r_sel05_buf, r_sel0[5]);
bufferH16$ buf10 (r_sel06_buf, r_sel0[6]);
bufferH16$ buf11 (r_sel07_buf, r_sel0[7]);

bufferH16$ buf12 (r_sel10_buf, r_sel1[0]);
bufferH16$ buf13 (r_sel11_buf, r_sel1[1]);
bufferH16$ buf14 (r_sel12_buf, r_sel1[2]);
bufferH16$ buf15 (r_sel13_buf, r_sel1[3]);
bufferH16$ buf16 (r_sel14_buf, r_sel1[4]);
bufferH16$ buf17 (r_sel15_buf, r_sel1[5]);
bufferH16$ buf18 (r_sel16_buf, r_sel1[6]);
bufferH16$ buf19 (r_sel17_buf, r_sel1[7]);

mux4_8$ mux0[3:0] (write_data0, result1, result2, result3, , r_sel00_buf, r_sel10_buf);
mux4_8$ mux1[3:0] (write_data1, result1, result2, result3, , r_sel01_buf, r_sel11_buf);
mux4_8$ mux2[3:0] (write_data2, result1, result2, result3, , r_sel02_buf, r_sel12_buf);
mux4_8$ mux3[3:0] (write_data3, result1, result2, result3, , r_sel03_buf, r_sel13_buf);
mux4_8$ mux4[3:0] (write_data4, result1, result2, result3, , r_sel04_buf, r_sel14_buf);
mux4_8$ mux5[3:0] (write_data5, result1, result2, result3, , r_sel05_buf, r_sel15_buf);
mux4_8$ mux6[3:0] (write_data6, result1, result2, result3, , r_sel06_buf, r_sel16_buf);
mux4_8$ mux7[3:0] (write_data7, result1, result2, result3, , r_sel07_buf, r_sel17_buf);

// Registers 
reg32e$ reg0 (.CLK(clk), .Din(write_data0), .Q(reg0_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[0]) );
reg32e$ reg1 (.CLK(clk), .Din(write_data1), .Q(reg1_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[1]) );
reg32e$ reg2 (.CLK(clk), .Din(write_data2), .Q(reg2_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[2]) );
reg32e$ reg3 (.CLK(clk), .Din(write_data3), .Q(reg3_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[3]) );
reg32e$ reg4 (.CLK(clk), .Din(write_data4), .Q(reg4_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[4]) );
reg32e$ reg5 (.CLK(clk), .Din(write_data5), .Q(reg5_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[5]) );
reg32e$ reg6 (.CLK(clk), .Din(write_data6), .Q(reg6_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[6]) );
reg32e$ reg7 (.CLK(clk), .Din(write_data7), .Q(reg7_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[7]) );

bufferH16$ bufs1 (SR10, SR1[0]);
bufferH16$ bufs2 (SR11, SR1[1]);
bufferH16$ bufs3 (SR12, SR1[2]);

bufferH16$ bufs4 (SR20, SR2[0]);
bufferH16$ bufs5 (SR21, SR2[1]);
bufferH16$ bufs6 (SR22, SR2[2]);

bufferH16$ bufs7 (SR30, SR3[0]);
bufferH16$ bufs8 (SR31, SR3[1]);
bufferH16$ bufs9 (SR32, SR3[2]);

bufferH16$ bufs10 (SR40, SR4[0]);
bufferH16$ bufs11 (SR41, SR4[1]);
bufferH16$ bufs12 (SR42, SR4[2]);

// Read SR1
mux4_8$ amux0[3:0] (out1m, reg0_out, reg1_out, reg2_out, reg3_out, SR10, SR11);
mux4_8$ amux1[3:0] (out2m, reg4_out, reg5_out, reg6_out, reg7_out, SR10, SR11);
mux2_8$ amux2[3:0] (regA, out1m, out2m, SR12);

//Read SR2
mux4_8$ bmux0[3:0] (out3m, reg0_out, reg1_out, reg2_out, reg3_out, SR20, SR21);
mux4_8$ bmux1[3:0] (out4m, reg4_out, reg5_out, reg6_out, reg7_out, SR20, SR21);
mux2_8$ bmux2[3:0] (regB, out3m, out4m, SR22);

// Read SR3
mux4_8$ cmux0[3:0] (out5m, reg0_out, reg1_out, reg2_out, reg3_out, SR30, SR31);
mux4_8$ cmux1[3:0] (out6m, reg4_out, reg5_out, reg6_out, reg7_out, SR30, SR31);
mux2_8$ cmux2[3:0] (regC, out5m, out6m, SR32);

// Read SR4
mux4_8$ dmux0[3:0] (out7m, reg0_out, reg1_out, reg2_out, reg3_out, SR40, SR41);
mux4_8$ dmux1[3:0] (out8m, reg4_out, reg5_out, reg6_out, reg7_out, SR40, SR41);
mux2_8$ dmux2[3:0] (regD, out7m, out8m, SR42);

endmodule
