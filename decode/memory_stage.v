// Size of control store needs to be changed
// address_out is also the address for dcache??

module memory_stage (
    input clk, set, reset,
    input [31:0] control_store, 
    input [31:0] EIP,
    input [15:0] CS,

    input [2:0] DR, SR, MM_DR, SEG_ID,
    input [1:0] data_size,
    input [31:0] address, 
    input [31:0] A, B,
    input [63:0] MM_A, MM_B,

    input [63:0] dcache_data,
    input dcache_ready,

    input type_A, type_B,
    input MM_type_A, MM_type_B,
    input operation, MM_operation,

    output dcache_en, 

    output [31:0] EIP_OUT,
    output [15:0] CS_OUT,
    output [31:0] control_store_OUT,
    output [2:0] DR_OUT, SR_OUT, MM_DR_OUT, SEG_ID_OUT,
    output [1:0] data_size_OUT,
    output [31:0] A_OUT, B_OUT,
    output [63:0] MM_A_OUT, MM_B_OUT,
    output [31:0] address_OUT,
    output operation_OUT, MM_operation_OUT
);

endmodule
