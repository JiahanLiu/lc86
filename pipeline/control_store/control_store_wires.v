wire CS_UOP_STALL_DE;
wire CS_MUX_OP_SIZE_D2;
wire [1:0] CS_OP_SIZE_D2;
wire CS_MUX_SR1_SIZE_D2;
wire CS_MUX_SR2_SIZE_D2;
wire [1:0] CS_SR2_SIZE_D2;
wire CS_MUX_DR1_SIZE_D2;
wire CS_MUX_DR2_SIZE_D2;
wire CS_IS_FAR_CALL_D2;
wire CS_MUX_MEM_RD_DE;
wire CS_MEM_RD_DE;
wire CS_JMP_STALL_DE;
wire CS_MUX_SR1_D2;
wire [2:0] CS_SR1_D2;
wire CS_MUX_SR2_D2;
wire [2:0] CS_SR2_D2;
wire CS_MUX_SEG1_D2;
wire CS_MUX_SEG2_D2;
wire CS_SR1_NEEDED_AG;
wire CS_SR2_NEEDED_AG;
wire CS_MUX_SEG1_NEEDED_AG;
wire CS_SEG1_NEEDED_AG;
wire CS_SEG2_NEEDED_AG;
wire CS_MM1_NEEDED_AG;
wire CS_MM2_NEEDED_AG;
wire [1:0] CS_MUX_A_AG;
wire CS_MUX_B_AG;
wire CS_MUX_DRID1_AG;
wire CS_MUX_EIP_JMP_REL_AG;
wire CS_MUX_NEXT_EIP_AG;
wire CS_MUX_NEXT_CSEG_AG;
wire CS_MUX_SP_ADD_SIZE_AG;
wire CS_MUX_TEMP_SP_AG;
wire CS_MUX_SP_PUSH_AG;
wire [1:0] CS_MUX_MEM_RD_ADDR_AG;
wire [1:0] CS_MUX_MEM_WR_ADDR_AG;
wire CS_MUX_IMM1_AG;
wire CS_MUX_B_ME;
wire CS_MUX_IMM_ADD_ME;
wire CS_IS_NEAR_RET_M2;
wire CS_IS_FAR_RET_M2;
wire CS_MUX_NEXT_EIP_M2;
wire CS_MUX_NEXT_CSEG_M2;
wire CS_IS_CMPS_FIRST_UOP_ALL;
wire CS_IS_CMPS_SECOND_UOP_ALL;
wire CS_REPNE_STEADY_STATE;
wire CS_IS_CMPXCHG_EX;
wire CS_LD_GPR1_D2;
wire [2:0] CS_DR1_D2;
wire CS_MUX_DR1_D2;
wire CS_LD_GPR2_EX;
wire CS_ALU_TO_B_EX;
wire [2:0] CS_DR2_D2;
wire CS_MUX_DR2_D2;
wire CS_DCACHE_WRITE_D2;
wire CS_MUX_MEM_WR_DE;
wire CS_LD_GPR3_WB;
wire [2:0] CS_DR3_WB;
wire [2:0] CS_ALUK_D2;
wire CS_MUX_ALUK_D2;
wire CS_IS_ALU32_EX;
wire CS_IS_ALU32_FLAGS_EX;
wire CS_IS_XCHG_EX;
wire CS_PASS_A_EX;
wire [1:0] CS_POP_SIZE_D2;
wire CS_MUX_SP_POP_EX;
wire CS_SAVE_NEIP_WB;
wire CS_SAVE_NCS_WB;
wire CS_PUSH_FLAGS_WB;
wire CS_POP_FLAGS_WB;
wire CS_USE_TEMP_NEIP_WB;
wire CS_USE_TEMP_NCS_WB;
wire CS_IS_JNBE_WB;
wire CS_IS_JNE_WB;
wire CS_LD_EIP_WB;
wire CS_LD_CS_WB;
wire CS_IS_CMOVC_WB;
wire CS_LD_SEG_WB;
wire CS_LD_MM_WB;
wire CS_MM_MEM_WB;
wire CS_LD_FLAGS_WB;
wire CS_IS_HALT_WB;
wire [6:0] CS_FLAGS_AFFECTED_WB;
wire CS_MUX_MICROSEQUENCER_DE;
wire [6:0] CS_NEXT_MICRO_ADDRESS_DE;
wire [12:0] PLACEHOLDER;
