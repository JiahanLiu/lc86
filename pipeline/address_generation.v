// 
module address_generation (
    input clk, set, reset,
    input [31:0] control_store, 
    input [31:0] EIP,
    input [15:0] CS,

    input [2:0] DR, SR, MM_DR, SEG_SR, SEG_DR,
    input [31:0] regA, regB, base, index,
    input [63:0] MM_A, MM_B,
    input [15:0] seg_addr, seg_src,
    input [1:0] data_size, 
    input [31:0] imm, disp,

    input operation, MM_operation,
    input type_A, type_B,
    input MM_type_A, MM_type_B,

    output [31:0] EIP_OUT,
    output [15:0] CS_OUT,
    output [31:0] control_store_OUT,
    output segment_limit_exception,

    output [2:0] DR_OUT, SR_OUT,
    output [2:0] MM_DR_OUT,
    output [2:0] SEG_ID_OUT,
    output [1:0] data_size_OUT,
    output type_A_OUT, type_B_OUT,
    output MM_type_A_OUT, MM_type_B_OUT,

    output [31:0] mem_address,
    output [31:0] A_OUT, B_OUT
    output [63:0] MM_A_OUT, MM_B_OUT,
    output operation_OUT, MM_operation_OUT
);

endmodule
