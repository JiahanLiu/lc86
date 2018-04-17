module modrm_decoder (
    input [7:0] modrm,
    output [2:0] SR, DR,
    output [2:0] MM_SR, MM_DR,
    output DE_LD_GPR_DE
);

and2$ and1 (DE_LD_GPR_DE, modrm[7], modrm[6]);
or2$ or1 (DE_MEM_RD_DE, modrm[7], modrm[6]);

assign DE_MEM_WR_DE = DE_MEM_RD_DE;

endmodule
