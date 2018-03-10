// 16 bytes from icache in one access

module fetch (
    input clk, set, reset,
    input [31:0] EIP,
    input [127:0] icache_data,
    input icache_ready,
    input [31:0] jmp_fp, trap_fp,
    input [15:0] CS,
    input [3:0] instr_length_updt,
    input [1:0] fp_mux,
    input load_eip,

    output [31:0] EIP_OUT,
    output [15:0] CS_OUT,
    output icache_en,
    output [31:0] icache_address,
    output segment_limit_exception,
    output [127:0] IR
);

endmodule
