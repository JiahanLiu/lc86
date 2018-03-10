// Control signals from writeback stage need to be defined

module writeback (
    input clk, set, reset, 
    input [31:0] control_store, 
    input [31:0] EIP,
    input [15:0] CS,

    input [2:0] DR, SR, MM_DR, SEG_ID,
    input [1:0] data_size,
    input [31:0] address, RESULT, XCHG_DATA, RESULT_FLAGS,
    input [63:0] MM_RESULT,

    input dcache_write_ready

    output control_signals,
    output v_xchg_flag, v_ld_gpr, v_ld_mm, v_ld_seg, v_ld_flags,
    output v_ld_eip, v_mem_write, MEM_write_stall
);

endmodule
