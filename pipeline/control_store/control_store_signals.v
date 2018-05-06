assign CS_UOP_STALL_DE = CONTROL_STORE[127:127];
assign CS_MUX_OP_SIZE_D2 = CONTROL_STORE[126:126];
assign CS_OP_SIZE_D2 = CONTROL_STORE[125:124];
assign CS_MUX_SR1_SIZE_D2 = CONTROL_STORE[123:123];
assign CS_MUX_SR2_SIZE_D2 = CONTROL_STORE[122:122];
assign CS_SR2_SIZE_D2 = CONTROL_STORE[121:120];
assign CS_MUX_DR1_SIZE_D2 = CONTROL_STORE[119:119];
assign CS_MUX_DR2_SIZE_D2 = CONTROL_STORE[118:118];
assign CS_IS_FAR_CALL_D2 = CONTROL_STORE[117:117];
assign CS_MUX_MEM_RD_DE = CONTROL_STORE[116:116];
assign CS_MEM_RD_DE = CONTROL_STORE[115:115];
assign CS_JMP_STALL_DE = CONTROL_STORE[114:114];
assign CS_MUX_SR1_D2 = CONTROL_STORE[113:113];
assign CS_SR1_D2 = CONTROL_STORE[112:110];
assign CS_MUX_SR2_D2 = CONTROL_STORE[109:109];
assign CS_SR2_D2 = CONTROL_STORE[108:106];
assign CS_MUX_SEG1_D2 = CONTROL_STORE[105:105];
assign CS_MUX_SEG2_D2 = CONTROL_STORE[104:104];
assign CS_SR1_NEEDED_AG = CONTROL_STORE[103:103];
assign CS_SR2_NEEDED_AG = CONTROL_STORE[102:102];
assign CS_MUX_SEG1_NEEDED_AG = CONTROL_STORE[101:101];
assign CS_SEG1_NEEDED_AG = CONTROL_STORE[100:100];
assign CS_SEG2_NEEDED_AG = CONTROL_STORE[99:99];
assign CS_MM1_NEEDED_AG = CONTROL_STORE[98:98];
assign CS_MM2_NEEDED_AG = CONTROL_STORE[97:97];
assign CS_MUX_A_AG = CONTROL_STORE[96:95];
assign CS_MUX_B_AG = CONTROL_STORE[94:94];
assign CS_MUX_DRID1_AG = CONTROL_STORE[93:93];
assign CS_MUX_EIP_JMP_REL_AG = CONTROL_STORE[92:92];
assign CS_MUX_NEXT_EIP_AG = CONTROL_STORE[91:91];
assign CS_MUX_NEXT_CSEG_AG = CONTROL_STORE[90:90];
assign CS_MUX_SP_ADD_SIZE_AG = CONTROL_STORE[89:89];
assign CS_MUX_TEMP_SP_AG = CONTROL_STORE[88:88];
assign CS_MUX_SP_PUSH_AG = CONTROL_STORE[87:87];
assign CS_MUX_MEM_RD_ADDR_AG = CONTROL_STORE[86:85];
assign CS_MUX_MEM_WR_ADDR_AG = CONTROL_STORE[84:83];
assign CS_MUX_IMM1_AG = CONTROL_STORE[82:82];
assign CS_MUX_B_ME = CONTROL_STORE[81:81];
assign CS_MUX_IMM_ADD_ME = CONTROL_STORE[80:80];
assign CS_IS_NEAR_RET_M2 = CONTROL_STORE[79:79];
assign CS_IS_FAR_RET_M2 = CONTROL_STORE[78:78];
assign CS_MUX_NEXT_EIP_M2 = CONTROL_STORE[77:77];
assign CS_MUX_NEXT_CSEG_M2 = CONTROL_STORE[76:76];
assign CS_IS_CMPS_FIRST_UOP_ALL = CONTROL_STORE[75:75];
assign CS_IS_CMPS_SECOND_UOP_ALL = CONTROL_STORE[74:74];
assign CS_REPNE_STEADY_STATE = CONTROL_STORE[73:73];
assign CS_IS_CMPXCHG_EX = CONTROL_STORE[72:72];
assign CS_LD_GPR1_D2 = CONTROL_STORE[71:71];
assign CS_DR1_D2 = CONTROL_STORE[70:68];
assign CS_MUX_DR1_D2 = CONTROL_STORE[67:67];
assign CS_LD_GPR2_EX = CONTROL_STORE[66:66];
assign CS_ALU_TO_B_EX = CONTROL_STORE[65:65];
assign CS_DR2_D2 = CONTROL_STORE[64:62];
assign CS_MUX_DR2_D2 = CONTROL_STORE[61:61];
assign CS_DCACHE_WRITE_D2 = CONTROL_STORE[60:60];
assign CS_MUX_MEM_WR_DE = CONTROL_STORE[59:59];
assign CS_LD_GPR3_WB = CONTROL_STORE[58:58];
assign CS_DR3_WB = CONTROL_STORE[57:55];
assign CS_ALUK_D2 = CONTROL_STORE[54:52];
assign CS_MUX_ALUK_D2 = CONTROL_STORE[51:51];
assign CS_IS_ALU32_EX = CONTROL_STORE[50:50];
assign CS_IS_ALU32_FLAGS_EX = CONTROL_STORE[49:49];
assign CS_IS_XCHG_EX = CONTROL_STORE[48:48];
assign CS_PASS_A_EX = CONTROL_STORE[47:47];
assign CS_MUX_SP_POP_EX = CONTROL_STORE[46:46];
assign CS_SAVE_NEIP_WB = CONTROL_STORE[45:45];
assign CS_SAVE_NCS_WB = CONTROL_STORE[44:44];
assign CS_PUSH_FLAGS_WB = CONTROL_STORE[43:43];
assign CS_POP_FLAGS_WB = CONTROL_STORE[42:42];
assign CS_USE_TEMP_NEIP_WB = CONTROL_STORE[41:41];
assign CS_USE_TEMP_NCS_WB = CONTROL_STORE[40:40];
assign CS_IS_JNBE_WB = CONTROL_STORE[39:39];
assign CS_IS_JNE_WB = CONTROL_STORE[38:38];
assign CS_LD_EIP_WB = CONTROL_STORE[37:37];
assign CS_LD_CS_WB = CONTROL_STORE[36:36];
assign CS_IS_CMOVC_WB = CONTROL_STORE[35:35];
assign CS_LD_SEG_WB = CONTROL_STORE[34:34];
assign CS_LD_MM_D2 = CONTROL_STORE[33:33];
assign CS_MM_MEM_WB = CONTROL_STORE[32:32];
assign CS_LD_FLAGS_WB = CONTROL_STORE[31:31];
assign CS_IS_HALT_WB = CONTROL_STORE[30:30];
assign CS_FLAGS_AFFECTED_WB = CONTROL_STORE[29:23];
assign CS_MUX_MICROSEQUENCER_DE = CONTROL_STORE[22:22];
assign CS_NEXT_MICRO_ADDRESS_DE = CONTROL_STORE[21:15];
assign PLACEHOLDER = CONTROL_STORE[14:0];
