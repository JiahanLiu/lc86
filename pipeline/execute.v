// Control store width needs to be adjusted

module execute (
    input clk, set, reset, 
    input [31:0] control_store,
    input [31:0] EIP,
    input [15:0] CS,

    input [2:0] DR, SR, MM_DR, SED_ID,
    input [1:0] data_size, 
    input [31:0] address,
    input [31:0] A, B,
    input [63:0] MM_A, MM_B,

    input operation, MM_operation,

    output [31:0] EIP_OUT,
    output [15:0] CS_OUT,
    output [31:0] control_store_out,
    output [2:0] DR_OUT, SR_OUT, MM_DR_OUT, SEG_ID_OUT,
    output [1:0] data_size_out,
    output [31:0] RESULT, XCHG_DATA, RESULT_FLAGS,
    output [31:0] address_OUT,
    output [63:0] MM_RESULT
);

endmodule
