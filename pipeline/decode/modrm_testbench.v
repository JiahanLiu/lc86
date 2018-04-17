`timescale 1ns/1ps

module TOP;
    reg [15:0] opcode;
    wire modrm_present;
    
    modrm_detector u_modrm_detector(.opcode(opcode), .modrm_present(modrm_present) );

    initial 
    begin

        #5
        opcode = 16'h0FFD;

        #5
        opcode = 16'h0F23;
    end

    initial begin
        $vcdplusfile ("modrm_detector.dump.vpd");
        $vcdpluson(0, TOP);
    end

    initial #20 $finish;

    always@(*) begin
        $strobe ("at time %0d, opcode = %h, modrm_present = %h", $time, opcode, modrm_present);
    end

endmodule
