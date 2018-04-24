`timescale 1ns/1ps

module TOP;
       
    reg clk;
    reg [31:0] result1, result2, result3;
    reg [2:0] SR1, SR2, SR3, SR4;
    reg [1:0]	RE1, RE2, RE3, RE4;
    reg [2:0] DR1, DR2, DR3;
    reg write_DR1, write_DR2, write_DR3;
    reg [1:0] WE1, WE2, WE3;
    wire [31:0] regA, regB, regC, regD;

    regfile8x32e regfile (clk, result1, result2, result3,
        SR1, SR2, SR3, SR4, RE1, RE2, RE3, RE4, 
        DR1, DR2, DR3, 
        write_DR1, write_DR2, write_DR3, 
        WE1, WE2, WE3, 
        regA, regB, regC, regD
    );

    initial 
    begin
        clk=0;
        regfile.reg0_ll.Q = 32'h0;
        regfile.reg1_ll.Q = 32'h1;
        regfile.reg2_ll.Q = 32'h2;
        regfile.reg3_ll.Q = 32'h3;
        regfile.reg4_ll.Q = 32'h4;
        regfile.reg5_ll.Q = 32'h5;
        regfile.reg6_ll.Q = 32'h6;
        regfile.reg7_ll.Q = 32'h7;

        regfile.reg0_lh.Q = 32'h800;
        regfile.reg1_lh.Q = 32'h900;
        regfile.reg2_lh.Q = 32'hA00;
        regfile.reg3_lh.Q = 32'hB00;
        regfile.reg4_lh.Q = 32'hC00;
        regfile.reg5_lh.Q = 32'hD00;
        regfile.reg6_lh.Q = 32'hE00;
        regfile.reg7_lh.Q = 32'hF00;

        regfile.reg0_hl.Q = 32'h00000;
        regfile.reg1_hl.Q = 32'h10000;
        regfile.reg2_hl.Q = 32'h20000;
        regfile.reg3_hl.Q = 32'h30000;
        regfile.reg4_hl.Q = 32'h40000;
        regfile.reg5_hl.Q = 32'h50000;
        regfile.reg6_hl.Q = 32'h60000;
        regfile.reg7_hl.Q = 32'h70000;

        regfile.reg0_hh.Q = 32'h8000000;
        regfile.reg1_hh.Q = 32'h9000000;
        regfile.reg2_hh.Q = 32'hA000000;
        regfile.reg3_hh.Q = 32'hB000000;
        regfile.reg4_hh.Q = 32'hC000000;
        regfile.reg5_hh.Q = 32'hD000000;
        regfile.reg6_hh.Q = 32'hE000000;
        regfile.reg7_hh.Q = 32'hF000000;

        write_DR1 = 1'b0;
        write_DR2 = 1'b0;
        write_DR3 = 1'b0;

        #5
        SR1=3'd5;
        SR2=3'd4;
        SR3=3'd2;
        SR4=3'd3;

        RE1=2'd0;
        RE2=2'd1;
        RE3=2'd2;
        RE4=2'd0;

        #10
        write_DR1 = 1'b1;
        write_DR2 = 1'b1;
        write_DR3 = 1'b1;

        result1 = 32'h6FA;
        result2 = 32'hEE97FA;
        result3 = 32'hBCBCD9FA;

        DR1=3'd5;
        DR2=3'd4;
        DR3=3'd2;

        WE1=2'd0;
        WE2=2'd1;
        WE3=2'd2;


        #3
        SR1=3'd1;
        SR2=3'd4;
        SR3=3'd2;
        SR4=3'd3;

        RE1=2'd2;
        RE2=2'd1;
        RE3=2'd2;
        RE4=2'd0;


    end

    initial begin
        $vcdplusfile ("reg.dump.vpd");
        $vcdpluson(0, TOP);
    end

    initial #50 $finish;

    always @(posedge clk) begin
        $strobe ("at time %0d, regA = %h", $time, regA);
        $strobe ("at time %0d, regB = %h", $time, regB);
        $strobe ("at time %0d, regC = %h", $time, regC);
        $strobe ("at time %0d, regD = %h", $time, regD);
    end

    always 
        #5 clk = !clk;

endmodule
