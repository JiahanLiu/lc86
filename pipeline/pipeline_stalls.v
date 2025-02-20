module PIPELINE(CLK, CLR, PRE, IR);
   //connect this to simulator
    input CLK, CLR, PRE;
    input [127:0] IR;
    assign EN = 1;//placeholder until stalls are working correctly
   
    //signals for EX generate WB bubbles or stalling
    wire WB_ld_latches;
    //signals from EX to Dependency Checks
    wire DEP_v_ex_ld_gpr1;
    wire DEP_v_ex_ld_gpr2;
    wire DEP_v_ex_ld_gpr3;
    wire Dep_v_ex_ld_seg;
    wire Dep_v_ex_ld_mm;
    wire Dep_v_ex_dcache_write;
    //signals from WB to Dependency Checks
    wire DEP_v_wb_ld_gpr1;
    wire DEP_v_wb_ld_gpr2;
    wire DEP_v_wb_ld_gpr3;
    wire DEP_v_wb_ld_seg;
    wire DEP_v_wb_ld_mm;
    wire DEP_v_wb_dcache_write;
    //signals from WB to dcache
    wire [2:0] WB_Final_DR1;
    wire [2:0] WB_Final_DR2;
    wire [2:0] WB_Final_DR3;
    wire [31:0] WB_Final_data1;
    wire [31:0] WB_Final_data2;
    wire [31:0] WB_Final_data3;
    wire WB_Final_ld_gpr1;
    wire WB_Final_ld_gpr2;
    wire WB_Final_ld_gpr3;
    wire [1:0] WB_Final_datasize;
    wire [1:0] WB_Final_DR3_datasize; 
    wire WB_Final_ld_seg; 
    wire [63:0] WB_Final_MM_Data;
    wire WB_Final_ld_mm; 
    wire [15:0] WB_Final_CS;
    wire WB_Final_ld_cs;
    wire [31:0] WB_Final_EIP; 
    wire WB_Final_ld_eip;
    wire [31:0] WB_Final_Flags;
    wire  WB_Final_ld_flags;
    wire [63:0] WB_Final_Dcache_Data;
    wire [31:0] WB_Final_Dcache_address;
    wire WB_Final_Dcache_Write; 
    //signals from d-cache needed by WB
    wire In_write_ready = 1'b1; //Steven 
    //WB outputs
    wire wb_halt_all;
    wire wb_repne_terminate_all;
    wire WB_stall;
    //Dataforwarded, currently for daa
    wire [31:0] flags_dataforwarded, count_dataforwarded;

   wire WB_EXC_V_OUT;
   wire WB_FLUSH_PIPELINE_BAR;
   wire INTERRUPT_SIGNAL = 1'b0; // TODO where does it come from
 
   wire WB_GEN_PROT_EXC_EXIST_V, WB_PAGE_FAULT_EXC_EXIST_V;

   // Dependency check outputs from stages
   wire AG_DEP_STALL_OUT;
   wire ME_MEM_DEP_STALL_OUT;
   //==================================
 
//*******REGISTER FILE*******//
   wire RST;
   wire [15:0] SEG_DIN;
   wire [2:0] 	SEGID1, SEGID2, WRSEGID;
   wire 	SEGWE;
   wire [63:0] MM_DIN;
   wire [2:0] 	MMID1, MMID2, WRMMID;
   wire 	MMWE;
   wire [31:0] GPR_DIN0, GPR_DIN1, GPR_DIN2;
   wire [2:0] 	GPRID0, GPRID1, GPRID2, GPRID3,	WRGPR0, WRGPR1, WRGPR2;
   wire [1:0] 	GPR_RE0, GPR_RE1, GPR_RE2, GPR_RE3, GPRWE0, GPRWE1, GPRWE2;
   wire WE0, WE1, WE2;     // WRITE ENABLE SIGNALS
   wire [15:0] CS_DIN;
   wire [31:0] EIP_DIN, EFLAGS_DIN;
   wire 	LD_CS, LD_EIP, LD_EFLAGS;
   wire [15:0] SEGDOUT1, SEGDOUT2;
   wire [63:0] MMDOUT1, MMDOUT2;
   wire [31:0] GPRDOUT0, GPRDOUT1, GPRDOUT2, GPRDOUT3;
   wire [15:0] CSDOUT;
   wire [31:0] EIPDOUT;
   wire [31:0] EFLAGSDOUT;

   // register data to address generation
   wire [31:0] SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA;
   assign SEG_DIN = WB_Final_data1[15:0];
   assign WRSEGID = WB_Final_DR1;
   assign SEGWE = WB_Final_ld_seg;
   assign MM_DIN = WB_Final_MM_Data;
   assign WRMMID = WB_Final_DR1;
   assign MMWE = WB_Final_ld_mm;
   assign GPR_DIN0 = WB_Final_data1;
   assign GPR_DIN1 =  WB_Final_data2;
   assign GPR_DIN2 = WB_Final_data3;
   assign WRGPR0 = WB_Final_DR1;
   assign WRGPR1 = WB_Final_DR2;
   assign WRGPR2 = WB_Final_DR3;
   //Jim Ask Apruv for Datasize inputs
   assign WE0 = WB_Final_ld_gpr1;
   assign WE1 = WB_Final_ld_gpr2;
   assign WE2 = WB_Final_ld_gpr3;
   assign CS_DIN = WB_Final_CS;
   assign LD_CS = WB_Final_ld_cs; 
   assign EIP_DIN = WB_Final_EIP;
   assign LD_EIP = WB_Final_ld_eip;
   assign EFLAGS_DIN = WB_Final_Flags;
   assign LD_EFLAGS = WB_Final_ld_flags;

   wire [15:0] SEG1_DATA, SEG2_DATA;
   wire [63:0] MM1_DATA, MM2_DATA;

   wire [2:0] REG_SEG1_ID, REG_SEG2_ID;
   wire [2:0] REG_MM1_ID, REG_MM2_ID;
   wire [2:0] REG_SR1_ID, REG_SR2_ID, REG_SR3_ID, REG_SR4_ID;
   wire [1:0] REG_SR1_SIZE, REG_SR2_SIZE, REG_SR3_SIZE, REG_SR4_SIZE;

// Make changes to the register file ports in the commented section- TODO
    register_file u_register_file (CLK, 
        SEG_DIN, REG_SEG1_ID, REG_SEG2_ID, WRSEGID, WB_Final_ld_seg,
        WB_Final_MM_Data, REG_MM1_ID, REG_MM2_ID, WRMMID, WB_Final_ld_mm, 
        WB_Final_data1, WB_Final_data2, WB_Final_data3,
        // GPR IDs
        REG_SR1_ID, REG_SR2_ID, REG_SR3_ID, REG_SR4_ID,
        // GPR Sizes
        REG_SR1_SIZE, REG_SR2_SIZE, REG_SR3_SIZE, REG_SR4_SIZE,
        WB_Final_DR1, WB_Final_DR2, WB_Final_DR3, WB_Final_datasize, WB_Final_datasize, WB_Final_DR3_datasize,
        // Enable signals from writeback
//        1'b0, 1'b0, 1'b0,
        WB_Final_ld_gpr1, WB_Final_ld_gpr2, WB_Final_ld_gpr3, 
        CS_DIN, WB_Final_EIP, EFLAGS_DIN,
        LD_CS, WB_Final_ld_eip, LD_EFLAGS,
        SEG1_DATA, SEG2_DATA, MM1_DATA, MM2_DATA,
        SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
        CSDOUT, EIPDOUT, EFLAGSDOUT, CLR
    );
       

//    register_file u_register_file (CLK, 
//        SEG_DIN, SEGID1, SEGID2, WRSEGID, SEGWE,
//        MM_DIN, MMID1, MMID2, WRMMID, MMWE, 
//        GPR_DIN0, GPR_DIN1, GPR_DIN2, 
//        D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT,
//        // For now, all the 4 read datasizes are same
//        2'd2, 2'd2, 2'd2, 2'd2,
//        // D2_DATA_SIZE_AG_OUT, D2_DATA_SIZE_AG_OUT, D2_DATA_SIZE_AG_OUT, D2_DATA_SIZE_AG_OUT,
//        WRGPR0, WRGPR1, WRGPR2, GPRWE0, GPRWE1, GPRWE2,
//        // Enable signals from writeback
//        // WE0, WE1, WE2,
//        1'b0, 1'b0, 1'b0,
//        CS_DIN, EIP_DIN, EFLAGS_DIN,
//        LD_CS, LD_EIP, LD_EFLAGS,
//        SEGDOUT1, SEGDOUT2, MMDOUT1, MMDOUT2,
//        SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
//        CSDOUT, EIPDOUT, EFLAGSDOUT, CLR
//    );

    //*******CACHE FILES*******//
    //Cache file systems to be used by the system
    wire [127:0] ICACHE_DOUT, DCACHE_DIN, DCACHE_DOUT;
    wire [31:0] ICACHE_PADDR_OUT, DC_PADDR;
    wire ICACHE_EN_OUT, DC_WE, ICACHE_READY, DC_R;	//ICACHE_EN_OUT needs to be included
    wire [4:0] FE_ICACHE_RD_SIZE_OUT;
    //icache u_icache (CLK, RST, ICACHE_PADDR_OUT, IC_R, IC_DOUT);
    //dcache u_dcache(CLK, RST, DC_PADDR, DC_DIN, DC_SIZE, DC_WE, DC_R, DC_DOUT);

    wire V_FETCH;
    wire [31:0] FETCH_POINTER;
    wire [4:0] ICACHE_SIZE_OUT;
    wire ICACHE_RW;
    wire ICACHE_RD_STALL;
    wire [127:0] IR_DATA_OUT;

   wire [127:0]  DCACHE_RD_DATA_OUT_LSU_IN;
   wire 	 DCACHE_READY_LSU_IN;
   wire [31:0] 	 LSU_OUT_DCACHE_ADDR_IN;
   wire [3:0] 	 LSU_OUT_DCACHE_SIZE_IN;
   wire 	 LSU_OUT_DCACHE_RW_IN;
   wire 	 LSU_OUT_DCACHE_EN;
   wire [63:0] 	 LSU_OUT_DCACHE_WR_DATA_IN;

   wire 	 LSU_OUT_RD_STALL, LSU_OUT_WR_STALL, LSU_OUT_WR_STALL_BAR;
   wire [63:0] 	 LSU_OUT_RD_DATA;
   
   wire WB_V_LSU_IN;
   wire WB_MEM_WR_LSU_IN;
   wire WB_WR_ADDR1_V_LSU_IN, WB_WR_ADDR2_V_LSU_IN;
   wire [31:0] WB_WR_ADDR1_LSU_IN, WB_WR_ADDR2_LSU_IN;
   wire [3:0] WB_WR_SIZE1_LSU_IN, WB_WR_SIZE2_LSU_IN;

   wire ME2_V_LSU_IN;
   wire ME2_MEM_RD_LSU_IN;
   wire ME2_RD_ADDR1_V_LSU_IN, ME2_RD_ADDR2_V_LSU_IN;
   wire [31:0] ME2_RD_ADDR1_LSU_IN, ME2_RD_ADDR2_LSU_IN;
   wire [3:0] ME2_RD_SIZE1_LSU_IN, ME2_RD_SIZE2_LSU_IN;
 
   wire v_mem_wr_lsu_in;
   assign WB_MEM_WR_LSU_IN = WB_Final_Dcache_Write;
   and2$ and_v_mem_wr_lsu_in (v_mem_wr_lsu_in, WB_V_LSU_IN, WB_MEM_WR_LSU_IN);

   wire v_mem_rd_lsu_in;
   and2$ and_v_mem_rd_lsu_in (v_mem_rd_lsu_in, ME2_V_LSU_IN, ME2_MEM_RD_LSU_IN);

   inv1$ inv_lsu_wr_stall (LSU_OUT_WR_STALL_BAR, LSU_OUT_WR_STALL);

//   lsu_controller u_lsu_controller (CLK, RST, 1'b1, V_MEM_RD, {rd_addr1_entry[23:4], LA_RD_ADDR[11:0]}, mux_rd_cross_size_out, rd_addr1_v, mux_rd_addr2_out, rd_addr2_cross_size, rd_addr2_v, V_MEM_WR, {wr_addr1_entry[23:4], LA_WR_ADDR[11:0]}, mux_wr_cross_size_out, wr_addr1_v, mux_wr_addr2_out, wr_addr2_cross_size, wr_addr2_v, WR_DATA, DCACHE_RD_DATA, DCACHE_READY, DCACHE_ADDR_OUT, DCACHE_SIZE_OUT, DCACHE_RW_OUT, dcache_en, DCACHE_WR_DATA_OUT, dcache_rd_stall, DCACHE_WR_STALL_OUT, RD_DATA_OUT);
   
   lsu_controller u_lsu_controller (
      CLK, CLR, PRE,
      v_mem_rd_lsu_in, 
      ME2_RD_ADDR1_LSU_IN, ME2_RD_SIZE1_LSU_IN, ME2_RD_ADDR1_V_LSU_IN,
      ME2_RD_ADDR2_LSU_IN, ME2_RD_SIZE2_LSU_IN, ME2_RD_ADDR2_V_LSU_IN,
      v_mem_wr_lsu_in,
      WB_WR_ADDR1_LSU_IN, WB_WR_SIZE1_LSU_IN, WB_WR_ADDR1_V_LSU_IN,
      WB_WR_ADDR2_LSU_IN, WB_WR_SIZE2_LSU_IN, WB_WR_ADDR2_V_LSU_IN,
      WB_Final_Dcache_Data,

      DCACHE_RD_DATA_OUT_LSU_IN, DCACHE_READY_LSU_IN,
      LSU_OUT_DCACHE_ADDR_IN, LSU_OUT_DCACHE_SIZE_IN, LSU_OUT_DCACHE_RW_IN,
      LSU_OUT_DCACHE_EN, LSU_OUT_DCACHE_WR_DATA_IN,

      LSU_OUT_RD_STALL, LSU_OUT_WR_STALL, LSU_OUT_RD_DATA
   );
   
    //*******FETCH STAGE*******//
    wire [31:0] FE_EIP_IN;	//this signal should be coming out of WB, does not need a latch
    wire [31:0] FE_JMP_FP, FE_TRAP_FP;//not sure where these signals come from yet
    wire [1:0] FE_FP_MUX;//not sure where this signal comes from yet
    wire FE_LD_EIP;//update the EIP!
    wire FE_SEG_LIM_EXC;//The fetch unit has an exception, needs more support

    wire DE_PRE_PRES_IN, DE_SEG_OVR_IN, DE_OP_OVR_IN, DE_RE_PRE_IN, DE_MODRM_PRES_IN, DE_IMM_PRES_IN, DE_SIB_PRES_IN;
    wire DE_DISP_PRES_IN, DE_DISP_SIZE_IN, DE_OFFSET_PRES_IN, DE_OP_SIZE_IN;
    wire [1:0] DE_IMM_SIZE_IN, DE_OFFSET_SIZE_IN, DE_PRE_SIZE_IN;
    wire [2:0] DE_DISP_SEL_IN, DE_SEGID_IN, DE_MODRM_SEL_IN;
    wire [3:0] DE_IMM_SEL_IN;
    wire [7:0] DE_MODRM_IN, DE_SIB_IN;
    wire [15:0] DE_OPCODE_IN;
    // Placeholder for now TODO: add selection for EIP when
    // interrupt/exceptions exist
    wire [15:0] DE_CS_IN; //= 16'h1A;
    wire [31:0] DE_EIP_IN; //= 32'h01;
    wire [31:0] DE_EIP_OUT, DE_EIP_OUT_BAR;
    wire [127:0] IR_IN;
    //Debug - change reg to wire
    //wire [127:0] IR;
    //reg [127:0] IR = 128'h83c00a00000000000000000000000000;
    wire [3:0] DE_INSTR_LENGTH_UPDT_IN;
    wire [3:0] DE_INSTR_LENGTH_UPDT_OUT; 
    wire [31:0] DE_INSTR_LENGTH_UPDT_OUT_T;
    wire [7:0] DE_CONTROL_STORE_ADDRESS_IN, DE_CONTROL_STORE_ADDRESS;
    wire [31:0] DE_CONTROL_STORE_ADDRESS_OUT;

    reg [127:0] temp_icache_data;
    reg icache_ready;
    assign ICACHE_DOUT = temp_icache_data;
    assign ICACHE_READY = icache_ready;
    //assign FE_EIP_IN = 32'b0;

//    initial begin
//       icache_ready = 1'b0;
//       #32
//       icache_ready = 1'b1;
//       #12
//       icache_ready = 1'b0;
//       #9
//       icache_ready = 1'b1;
//       #12 icache_ready = 1'b0;
//       #10
//       icache_ready = 1'b1;
//       #12
//       icache_ready = 1'b0;
//       #15
//       icache_ready = 1'b1;
//    end
    always @(posedge icache_ready) begin
       #12
       icache_ready = 1'b0;
    end
    always @(ICACHE_PADDR_OUT) begin
       icache_ready = 1'b0;
    end
    always @(ICACHE_PADDR_OUT or posedge CLK or ICACHE_EN_OUT) begin
       if (ICACHE_EN_OUT) begin
          $strobe("ICACHE_RD_ADDR %0h size %0h @ time %0t", ICACHE_PADDR_OUT, FE_ICACHE_RD_SIZE_OUT, $time);
          if (ICACHE_PADDR_OUT[7:0] == 8'h00) begin
             //temp_icache_data = 128'h0F6FEB254B212F9681773D090CDB1283;
             //temp_icache_data = 128'h8312DB0C093D7781962F214B25EB6F0F;
             //temp_icache_data = 128'h1504AB230566441205F205;
             temp_icache_data = 128'h23643484B10F;
             $strobe("icache data 0 %0h", temp_icache_data);
          end
          else if (ICACHE_PADDR_OUT[7:0] == 8'h10) begin
             //temp_icache_data = 128'h7E6D39201F21D32285BC148878235B49;
             temp_icache_data = 128'h495B23788814BC8522D3211F29386D7E;
             $strobe("icache data 1 %0h", temp_icache_data);
          end
          else if (ICACHE_PADDR_OUT[7:0] == 8'h20) begin
             //temp_icache_data = 128'h0F6FEB254B212F9681773D090CDB1283;
             temp_icache_data = 128'h8312DB0C093D7781962F214B25EB6F0F;
             $strobe("icache data 2 %0h", temp_icache_data);
          end
          else if (ICACHE_PADDR_OUT[7:0] == 8'h30) begin
             //temp_icache_data = 128'h7E6D39201F21D32285BC148878235B49;;
             temp_icache_data = 128'h495B23788814BC8522D3211F29386D7E;
             $strobe("icache data 3 %0h", temp_icache_data);
          end
       end
       #10
       icache_ready = 1'b1;
    end
             
    wire INT_EXIST_DE_IN;
    or2$ or_de_exc_v (INT_EXIST_DE_IN, WB_EXC_V_OUT, INTERRUPT_SIGNAL);

    wire DEP_AND_MEM_STALLS, DEP_AND_MEM_STALLS_BAR;
    assign FE_EIP_IN = EIPDOUT;

    wire FETCH_STALL_OUT, FETCH_PAGE_FAULT_EXC_EXIST_OUT;

    fetch u_fetch (
        CLK, CLR, PRE, 

        FE_EIP_IN, 
        CSDOUT,

        ICACHE_DOUT, 
        ICACHE_READY,
    	      
        FE_JMP_FP, FE_TRAP_FP,
        FE_FP_MUX,
        FE_LD_EIP,
    
        DEP_AND_MEM_STALLS, DEP_AND_MEM_STALLS_BAR, 1'b0, 1'b0,
        INT_EXIST_DE_IN,

        // outputs to next stage
        DE_EIP_IN,
        DE_CS_IN,

        // outputs to ICACHE
        ICACHE_PADDR_OUT,
        FE_ICACHE_RD_SIZE_OUT,
        ICACHE_EN_OUT,

        FE_SEG_LIM_EXC,
        IR_IN,

        DE_INSTR_LENGTH_UPDT_IN,
        DE_OPCODE_IN,
        DE_PRE_SIZE_IN,
        DE_PRE_PRES_IN,  DE_SEG_OVR_IN,  DE_OP_OVR_IN,  DE_RE_PRE_IN, 
        DE_MODRM_PRES_IN,  DE_IMM_PRES_IN, 
        DE_IMM_SIZE_IN, 
        DE_SIB_PRES_IN,  DE_DISP_PRES_IN,  DE_DISP_SIZE_IN, 
        DE_IMM_SEL_IN, 
        DE_DISP_SEL_IN, 
        DE_OFFSET_PRES_IN, 
        DE_OP_SIZE_IN, 
        DE_OFFSET_SIZE_IN, 
        DE_SEGID_IN, 
        DE_MODRM_IN,  DE_SIB_IN, 
        DE_MODRM_SEL_IN,
        DE_CONTROL_STORE_ADDRESS_IN,

        FETCH_STALL_OUT, FETCH_PAGE_FAULT_EXC_EXIST_OUT
    ); 

//    decode_stage1 u_decode_stage1 (
//        CLK, PRE, CLR,
//        IR,
//        // interrupt enable inputs
//        INT_EXIST_DE_IN,
//
//        // outputs
//        IR_IN,
//        DE_INSTR_LENGTH_UPDT_IN,
//        DE_OPCODE_IN,
//        DE_PRE_SIZE_IN,
//        DE_PRE_PRES_IN,  DE_SEG_OVR_IN,  DE_OP_OVR_IN,  DE_RE_PRE_IN, 
//        DE_MODRM_PRES_IN,  DE_IMM_PRES_IN, 
//        DE_IMM_SIZE_IN, 
//        DE_SIB_PRES_IN,  DE_DISP_PRES_IN,  DE_DISP_SIZE_IN, 
//        DE_IMM_SEL_IN, 
//        DE_DISP_SEL_IN, 
//        DE_OFFSET_PRES_IN, 
//        DE_OP_SIZE_IN, 
//        DE_OFFSET_SIZE_IN, 
//        DE_SEGID_IN, 
//        DE_MODRM_IN,  DE_SIB_IN, 
//        DE_MODRM_SEL_IN,
//        DE_CONTROL_STORE_ADDRESS_IN
//    );

   wire DE_V_IN, LD_D2, and0_ld_d2_out;
   wire AG_STALL_OUT_LD_D2_IN;
   wire D2_UOP_STALL_OUT, D2_UOP_STALL_OUT_BAR;

   wire D2_EXC_EN_V_OUT, AG_EXC_EN_V_OUT, AG2_EXC_EN_V_OUT,
        ME_EXC_EN_V_OUT, ME2_EXC_EN_V_OUT, EX_EXC_EN_V_OUT;

   wire nor0_de_v_exc_out, nor1_de_v_exc_out, and0_de_v_out;
   nor4$ nor0_de_v_exc (nor0_de_v_exc_out, FETCH_STALL_OUT, D2_EXC_EN_V_OUT, AG_EXC_EN_V_OUT, AG2_EXC_EN_V_OUT);
   nor4$ nor1_de_v_exc (nor1_de_v_exc_out, ME_EXC_EN_V_OUT, ME2_EXC_EN_V_OUT, EX_EXC_EN_V_OUT, wb_repne_terminate_all);

//   nor4$ nor2_de_v_jmp (nor2_de_v_jmp_out, D2
   and2$ and0_de_v (and0_de_v_out, nor0_de_v_exc_out, nor1_de_v_exc_out);
   or3$ or0_de_v (DE_V_IN, and0_de_v_out, WB_EXC_V_OUT, INTERRUPT_SIGNAL);

   // assign DE_V_IN = 1'b1;
   // DE_V_IN = (!FETCH_STALL && !FE_PAGE_FAULT_EXC && !D2_EXC_EN_OUT && !AG_EXC_EN_OUT &&
   // !AG2_EXC_EN_OUT && !ME_EXC_EN_OUT && !ME2_EXC_EN_OUT  && !EX_EXC_EN_OUT
   // && !wb_repne_terminate_all) || WB_EXC_V_OUT || INTERRUPT_SIGNAL
   //
   // TODO LD_D2 = !REG_DEP_STALL && ! MEM_DEP_STALL && !MEM_RD_STALL && !MEM_WR_STALL && !UOP_STALL
   // || WB_V && (PAGE_FAULT | GPROT_EXC) || INT_SIGNAL
   // wire LD_D2 = 1'b1;
   inv1$ inv_uop_stall (D2_UOP_STALL_OUT_BAR, D2_UOP_STALL_OUT);
   and2$ and_ld_d2_stall (and0_ld_d2_out, AG_STALL_OUT_LD_D2_IN, D2_UOP_STALL_OUT_BAR);
   or3$ or0_ld_d2 (LD_D2, and0_ld_d2_out, WB_EXC_V_OUT, INTERRUPT_SIGNAL);

   assign DEP_AND_MEM_STALLS_BAR = and0_ld_d2_out;
   inv1$ inv_dep_mem_stalls (DEP_AND_MEM_STALLS, DEP_AND_MEM_STALLS_BAR);

   // Latches between fetch and decode
   wire [31:0] DE_V_OUT_T, DE_V_OUT_T_BAR, DE_OP_CS_OUT_T, DE_OP_CS_OUT_T_BAR, MOD_SIB_OUT, MOD_SIB_OUT_BAR;	//temp wires
   wire [127:0] IR_OUT, IR_BAR_OUT;
   reg32e$ MOD_SIB(CLK, {16'b0, DE_MODRM_IN, DE_SIB_IN}, MOD_SIB_OUT, MOD_SIB_OUT_BAR, CLR, PRE, LD_D2);
   reg32e$ IR_3(CLK, IR_IN[127:96], IR_OUT[127:96], IR_BAR_OUT[127:96], CLR, PRE, LD_D2);
   reg32e$ IR_2(CLK, IR_IN[95:64], IR_OUT[95:64], IR_BAR_OUT[95:64], CLR, PRE, LD_D2);
   reg32e$ IR_1(CLK, IR_IN[63:32], IR_OUT[63:32], IR_BAR_OUT[63:32], CLR, PRE, LD_D2);
   reg32e$ IR_0(CLK, IR_IN[31:0], IR_OUT[31:0], IR_BAR_OUT[31:0], CLR, PRE, LD_D2);
   reg32e$ DE_EIP(CLK, DE_EIP_IN, DE_EIP_OUT, DE_EIP_OUT_BAR, CLR, PRE, LD_D2);
   reg32e$ DE_V(CLK, {1'b0, DE_DISP_PRES_IN, DE_DISP_SIZE_IN, DE_OFFSET_PRES_IN, DE_OP_SIZE_IN, DE_PRE_PRES_IN, 
                DE_SEG_OVR_IN, DE_OP_OVR_IN, DE_RE_PRE_IN, DE_MODRM_PRES_IN, DE_IMM_PRES_IN, DE_SIB_PRES_IN, 
                DE_IMM_SEL_IN, DE_DISP_SEL_IN, DE_SEGID_IN, DE_MODRM_SEL_IN, DE_IMM_SIZE_IN, DE_OFFSET_SIZE_IN, 
                DE_PRE_SIZE_IN, DE_V_IN}, DE_V_OUT_T, DE_V_OUT_T_BAR, CLR, PRE, LD_D2);	//used for various values 

   reg32e$ DE_OP_CS(CLK, {DE_OPCODE_IN, DE_CS_IN}, DE_OP_CS_OUT_T, DE_OP_CS_OUT_T_BAR, CLR, PRE, LD_D2); 
   reg32e$ INSTR_LENGTH (CLK, {28'b0, DE_INSTR_LENGTH_UPDT_IN}, DE_INSTR_LENGTH_UPDT_OUT_T, ,CLR, PRE, LD_D2);
   reg32e$ DE_CNTRL_ADDR (CLK, {24'b0, DE_CONTROL_STORE_ADDRESS_IN}, DE_CONTROL_STORE_ADDRESS_OUT, , CLR, PRE, LD_D2);

 
   assign DE_CONTROL_STORE_ADDRESS = DE_CONTROL_STORE_ADDRESS_OUT[7:0];
   wire D2_V = DE_V_OUT_T[0];
   wire [1:0] DE_PRE_SIZE_OUT = DE_V_OUT_T[2:1];
   wire [1:0] DE_OFFSET_SIZE_OUT = DE_V_OUT_T[4:3];
   wire [1:0] DE_IMM_SIZE_OUT = DE_V_OUT_T[6:5];
   wire [2:0] DE_MODRM_SEL_OUT = DE_V_OUT_T[9:7];
   wire [2:0] DE_SEGID_OUT = DE_V_OUT_T[12:10];
   wire [2:0] DE_DISP_SEL_OUT = DE_V_OUT_T[15:13];
   wire [3:0] DE_IMM_SEL_OUT = DE_V_OUT_T[19:16];
   wire DE_SIB_PRES_OUT = DE_V_OUT_T[20];
   wire DE_IMM_PRES_OUT = DE_V_OUT_T[21]; 
   wire DE_MODRM_PRES_OUT = DE_V_OUT_T[22];
   wire DE_RE_PRE_OUT = DE_V_OUT_T[23]; 
   wire DE_OP_OVR_OUT = DE_V_OUT_T[24]; 
   wire DE_SEG_OVR_OUT = DE_V_OUT_T[25];
   wire DE_PRE_PRES_OUT = DE_V_OUT_T[26]; 
   wire DE_OP_SIZE_OUT = DE_V_OUT_T[27]; 
   wire DE_OFFSET_PRES_OUT = DE_V_OUT_T[28];
   wire DE_DISP_SIZE_OUT = DE_V_OUT_T[29]; 
   wire DE_DISP_PRES_OUT = DE_V_OUT_T[30];
   wire [7:0] DE_SIB_OUT = MOD_SIB_OUT[7:0];
   wire [7:0] DE_MODRM_OUT = MOD_SIB_OUT[15:8];

   wire [15:0] DE_OPCODE_OUT = DE_OP_CS_OUT_T[31:16];
   wire [15:0] DE_CS_OUT = DE_OP_CS_OUT_T[15:0];
   wire [3:0] DE_INSTR_LENGTH_UPDATE_OUT = DE_INSTR_LENGTH_UPDT_OUT_T[3:0];

   // Outputs from Decode Stage 2
   wire [31:0] D2_EIP_OUT;
   wire [15:0] D2_CS_OUT;
   wire [127:0] D2_CONTROL_STORE_OUT;

   wire [47:0] D2_OFFSET_OUT;

   wire D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT, D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT;
   wire [2:0] D2_ALUK_EX_OUT;
   wire D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT;
   wire [31:0] D2_IMM32_OUT, D2_DISP32_OUT;
   wire D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG, D2_MUX_SEG_AG, D2_CMPXCHG_AG;
   wire [1:0] D2_SIB_S_AG;

   wire [2:0] D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT;

   wire [1:0] D2_SR1_SIZE_AG_OUT, D2_SR2_SIZE_AG_OUT;
   wire [1:0] D2_DR1_SIZE_WB_OUT, D2_DR2_SIZE_WB_OUT;
   wire [1:0] D2_MEM_SIZE_WB_OUT;

   wire D2_PAGE_FAULT_EXC_EXIST_OUT;
   wire D2_NMI_INT_EN_OUT, D2_GEN_PROT_EXC_EN_OUT, D2_PAGE_FAULT_EXC_EN_OUT;
   wire D2_REPNE_WB_OUT;

   // save interrupt status
   wire [31:0] D2_PS_SAVE_INT_STATUS;
   reg32e$ d2_save_int_status (CLK, {28'b0, FETCH_PAGE_FAULT_EXC_EXIST_OUT, INTERRUPT_SIGNAL, WB_GEN_PROT_EXC_EXIST_V, WB_PAGE_FAULT_EXC_EXIST_V}, D2_PS_SAVE_INT_STATUS, , CLR, PRE, LD_D2);

   wire D2_PS_PAGE_FAULT_EXC_EXIST;
   wire D2_PS_NMI_INT_EN, D2_PS_GEN_PROT_EXC_EN, D2_PS_PAGE_FAULT_EXC_EN;
   assign {D2_PS_PAGE_FAULT_EXC_EXIST, D2_PS_NMI_INT_EN, D2_PS_GEN_PROT_EXC_EN, D2_PS_PAGE_FAULT_EXC_EN} = D2_PS_SAVE_INT_STATUS[3:0];

//    wire [2:0] AG_DRID1, AG_DRID2;
//    wire V_AG_LD_GPR1, V_AG_LD_GPR2, V_AG_LD_SEG, V_AG_LD_CSEG, V_AG_LD_MM;
//    wire [2:0] ME_DRID1, ME_DRID2;
//    wire V_ME_LD_GPR1, V_ME_LD_GPR2, V_ME_LD_SEG, V_ME_LD_CSEG, V_ME_LD_MM;
//    wire [2:0] EX_DRID1, EX_DRID2;
//    wire V_EX_LD_GPR1, V_EX_LD_GPR2, V_EX_LD_SEG, V_EX_LD_CSEG, V_EX_LD_MM;

   wire d2_ps_v_stage_in, d2_ps_page_fault_exc_exist_bar;
   inv1$ inv_d2_ps_page_fault_exc_exist (d2_ps_page_fault_exc_exist_bar, D2_PS_PAGE_FAULT_EXC_EXIST);
   and2$ and_d2_v_stage_in (d2_ps_v_stage_in, D2_V, d2_ps_page_fault_exc_exist_bar);

//*******DECODE STAGE 2*******//
   decode_stage2 u_decode_stage2(
      CLK, PRE, CLR,
      d2_ps_v_stage_in,
      IR_OUT, 
      DE_EIP_OUT,
      DE_CS_OUT,
      DE_INSTR_LENGTH_UPDATE_OUT,
      DE_OPCODE_OUT, 
      DE_PRE_SIZE_OUT,
      DE_PRE_PRES_OUT, DE_SEG_OVR_OUT, DE_OP_OVR_OUT, DE_RE_PRE_OUT, 
      DE_MODRM_PRES_OUT, DE_IMM_PRES_OUT,
      DE_IMM_SIZE_OUT,
      DE_SIB_PRES_OUT, DE_DISP_PRES_OUT, DE_DISP_SIZE_OUT,
      DE_IMM_SEL_OUT,
      DE_DISP_SEL_OUT,
      DE_MODRM_SEL_OUT,
      DE_OFFSET_PRES_OUT,
      DE_OP_SIZE_OUT, 
      DE_OFFSET_SIZE_OUT,
      DE_SEGID_OUT,
      DE_MODRM_OUT, DE_SIB_OUT,
      DE_CONTROL_STORE_ADDRESS,

      D2_PS_NMI_INT_EN, D2_PS_GEN_PROT_EXC_EN, D2_PS_PAGE_FAULT_EXC_EN,
      D2_PS_PAGE_FAULT_EXC_EXIST,

      INT_EXIST_DE_IN,

      D2_EIP_OUT, 
      D2_CS_OUT,
      D2_CONTROL_STORE_OUT,
      D2_OFFSET_OUT,
                      
      D2_SR1_SIZE_AG_OUT, D2_SR2_SIZE_AG_OUT,
      D2_DR1_SIZE_WB_OUT, D2_DR2_SIZE_WB_OUT,
      D2_MEM_SIZE_WB_OUT,

      D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT,

      D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT, 
      D2_ALUK_EX_OUT,
      D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,

      D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT,
      D2_IMM32_OUT, D2_DISP32_OUT,

      D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG,
      D2_MUX_SEG_AG, D2_CMPXCHG_AG,
      D2_SIB_S_AG,

      D2_PAGE_FAULT_EXC_EXIST_OUT,
      D2_NMI_INT_EN_OUT, D2_GEN_PROT_EXC_EN_OUT, D2_PAGE_FAULT_EXC_EN_OUT,
      D2_REPNE_WB_OUT, D2_UOP_STALL_OUT, D2_EXC_EN_V_OUT
   );

   wire [31:0] AG_PS_EIP;
   wire [15:0] AG_PS_CS, AG_PS_CS_NC;
   wire AG_PS_REPNE_WB;
   
   wire [127:0] AG_PS_CONTROL_STORE;
   wire [47:0] 	AG_PS_OFFSET;
   
   wire AG_PS_D2_SR1_NEEDED_AG, AG_PS_D2_SEG1_NEEDED_AG, AG_PS_D2_MM1_NEEDED_AG;

   wire AG_PS_D2_MEM_RD_ME, AG_PS_D2_MEM_WR_ME;
   wire [2:0] AG_PS_D2_ALUK_EX;
   wire AG_PS_D2_LD_GPR1_WB, AG_PS_D2_LD_MM_WB;

   wire [2:0] AG_PS_SR1, AG_PS_SR2, AG_PS_SR3, AG_PS_SIB_I, AG_PS_SEG1, AG_PS_SEG2;

   wire [1:0] AG_PS_D2_SR1_SIZE_AG, AG_PS_D2_SR2_SIZE_AG;
   wire [1:0] AG_PS_D2_DR1_SIZE_WB, AG_PS_D2_DR2_SIZE_WB;
   wire [1:0] AG_PS_D2_MEM_SIZE_WB;

   wire [31:0] AG_PS_IMM32, AG_PS_DISP32;

   wire AG_PS_DE_SIB_EN_AG, AG_PS_DE_DISP_EN_AG, AG_PS_DE_BASE_REG_EN_AG;
   wire AG_PS_DE_MUX_SEG_AG, AG_PS_DE_CMPXCHG_AG;
   wire [1:0] AG_PS_DE_SIB_S_AG;

   wire AG_PS_PAGE_FAULT_EXC_EXIST;
   wire AG_PS_NMI_INT_EN, AG_PS_GEN_PROT_EXC_EN, AG_PS_PAGE_FAULT_EXC_EN;
   
   // Signals to register file
   wire [2:0] AG_SR1_OUT, AG_SR2_OUT, AG_SR3_OUT, AG_SIB_I_OUT, AG_SEG1_OUT, AG_SEG2_OUT, AG_MM1_OUT, AG_MM2_OUT;

   wire [1:0] AG_D2_SR1_SIZE_AG_OUT, AG_D2_SR2_SIZE_AG_OUT;
   wire [1:0] AG_D2_SR3_SIZE_AG_OUT, AG_D2_SR4_SIZE_AG_OUT;
   wire [1:0] AG_D2_DR1_SIZE_WB_OUT, AG_D2_DR2_SIZE_WB_OUT;
   wire [1:0] AG_D2_MEM_SIZE_WB_OUT;
   
   // Register file assignments
   assign REG_SR1_ID = AG_SR1_OUT;
   assign REG_SR2_ID = AG_SR2_OUT;
   assign REG_SR3_ID = AG_SR3_OUT;
   assign REG_SR4_ID = AG_SIB_I_OUT;

   assign REG_SEG1_ID = AG_SEG1_OUT;
   assign REG_SEG2_ID = AG_SEG2_OUT;

   assign REG_MM1_ID = AG_MM1_OUT;
   assign REG_MM2_ID = AG_MM2_OUT;

   assign REG_SR1_SIZE = AG_D2_SR1_SIZE_AG_OUT;
   assign REG_SR2_SIZE = AG_D2_SR2_SIZE_AG_OUT;
   assign REG_SR3_SIZE = AG_D2_SR3_SIZE_AG_OUT;
   assign REG_SR4_SIZE = AG_D2_SR4_SIZE_AG_OUT;
   //===================================

   // Signals for next stage latches
   wire [31:0] AG_EIP_OUT; // for CS segment check
   wire [31:0] AG_NEIP_OUT;
   wire [15:0] AG_NCS_OUT;
   wire [127:0] AG_CONTROL_STORE_OUT;

   wire AG_REPNE_WB_OUT; 
   wire [31:0] AG_A_OUT, AG_B_OUT;
   wire [63:0] AG_MM_A_OUT, AG_MM_B_OUT;
   wire [31:0] AG_SP_XCHG_DATA_OUT;
   wire [31:0] AG_ADD_BASE_DISP_OUT, AG_ADD_SIB_SEG1_OUT;
   wire [31:0] AG_SIB_SI_DATA_OUT;
   wire [15:0] AG_SEG1_DATA_OUT;
   wire [15:0] AG_SEG2_DATA_OUT;
   wire [31:0] AG_INTERRUPT_ADDR_OUT;
   
   wire [2:0]  AG_D2_ALUK_EX_OUT;
   wire [2:0]  AG_DRID1_OUT, AG_DRID2_OUT;

   wire        AG_D2_MEM_RD_ME_OUT, AG_D2_MEM_WR_WB_OUT;
   wire        AG_D2_LD_GPR1_WB_OUT, AG_D2_LD_MM_WB_OUT;
   //wire        AG_DEP_STALL_OUT;

   wire        AG_PAGE_FAULT_EXC_EXIST_OUT;
   
   wire [31:0] D2_OUT1_AG_PS, D2_OUT2_AG_PS, AG_PS_IN1, AG_PS_IN2;
   wire [31:0] D2_CS_OUT32;

   wire D2_AG_V_OUT, AG_PS_V;
   // TODO AG_V = D2_V
   and2$ and_ag_v (D2_AG_V_OUT, D2_V, WB_FLUSH_PIPELINE_BAR);
   // assign D2_AG_V_OUT = 1'b1;

   wire LD_AG;
   wire AG2_PS_V_OUT_AG_IN, ME_PS_V_OUT_AG_IN, ME2_PS_V_OUT_AG_IN, EX_PS_V_OUT_AG_IN;

   wire [23:0] AG_GPR_SCOREBOARD_OUT;
   wire [7:0] AG_SEG_SCOREBOARD_OUT;
   wire [7:0] AG_MM_SCOREBOARD_OUT;

   wire [23:0] AG2_GPR_SCOREBOARD_OUT, ME_GPR_SCOREBOARD_OUT, ME2_GPR_SCOREBOARD_OUT, EX_GPR_SCOREBOARD_OUT;
   wire [7:0] AG2_SEG_SCOREBOARD_OUT, ME_SEG_SCOREBOARD_OUT, ME2_SEG_SCOREBOARD_OUT, EX_SEG_SCOREBOARD_OUT;
   wire [7:0] AG2_MM_SCOREBOARD_OUT, ME_MM_SCOREBOARD_OUT, ME2_MM_SCOREBOARD_OUT, EX_MM_SCOREBOARD_OUT;

   // LD_AG = !REG_DEP_STALL && !MEM_DEP_STALL && !MEM_RD_STALL && !MEM_WR_STALL
   // assign LD_AG = 1'b1;
   nor4$ nor_ld_ag (LD_AG, AG_DEP_STALL_OUT, ME_MEM_DEP_STALL_OUT, LSU_OUT_RD_STALL, LSU_OUT_WR_STALL);
   assign AG_STALL_OUT_LD_D2_IN = LD_AG;

   reg32e$
      u_reg_ag_ps_eip (CLK, D2_EIP_OUT, AG_PS_EIP, , CLR, PRE, LD_AG),
      u_reg_ag_ps_cs (CLK, {16'b0, D2_CS_OUT}, {AG_PS_CS_NC, AG_PS_CS}, , CLR, PRE, LD_AG);

   reg64e$
     u_reg_ag_ps_control_store0 (CLK, D2_CONTROL_STORE_OUT[127:64], AG_PS_CONTROL_STORE[127:64], , CLR, PRE, LD_AG),
     u_reg_ag_ps_control_store1 (CLK, D2_CONTROL_STORE_OUT[63:0], AG_PS_CONTROL_STORE[63:0], , CLR, PRE, LD_AG);

   // [31:2]
   assign D2_OUT1_AG_PS[31:1] = { D2_AG_V_OUT, D2_PAGE_FAULT_EXC_EXIST_OUT,
          D2_SR1_NEEDED_AG_OUT, D2_SEG1_NEEDED_AG_OUT, D2_MM1_NEEDED_AG_OUT,
          D2_MEM_RD_ME_OUT, D2_MEM_WR_ME_OUT, D2_ALUK_EX_OUT, D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,
          D2_SR1_OUT, D2_SR2_OUT, D2_SR3_OUT, D2_SIB_I_OUT, D2_SEG1_OUT, D2_SEG2_OUT , D2_REPNE_WB_OUT};

   wire [63:0] AG_PS_OFFSET_OUT;
    // reg32e$ IR_1(CLK, IR_IN[63:32], IR_OUT[63:32], IR_BAR_OUT[63:32], CLR, PRE, EN);
   reg32e$
      u_reg_ag_ps_in1 (CLK, D2_OUT1_AG_PS, AG_PS_IN1, , CLR, PRE, LD_AG),
      u_reg_ag_ps_imm32 (CLK, D2_IMM32_OUT, AG_PS_IMM32, , CLR, PRE, LD_AG),
      u_reg_ag_ps_disp32 (CLK, D2_DISP32_OUT, AG_PS_DISP32, , CLR, PRE, LD_AG),
      u_reg_ag_ps_offset32 (CLK, D2_OFFSET_OUT[31:0], AG_PS_OFFSET_OUT[31:0], , CLR, PRE, LD_AG),
      u_reg_ag_ps_offset16 (CLK, {16'h0, D2_OFFSET_OUT[47:32]}, AG_PS_OFFSET_OUT[63:32], , CLR, PRE, LD_AG);

   assign AG_PS_OFFSET = AG_PS_OFFSET_OUT[47:0];
   assign { AG_PS_V, AG_PS_PAGE_FAULT_EXC_EXIST, 
            AG_PS_D2_SR1_NEEDED_AG, AG_PS_D2_SEG1_NEEDED_AG, AG_PS_D2_MM1_NEEDED_AG,
            AG_PS_D2_MEM_RD_ME, AG_PS_D2_MEM_WR_ME, AG_PS_D2_ALUK_EX, AG_PS_D2_LD_GPR1_WB, AG_PS_D2_LD_MM_WB,
            AG_PS_SR1, AG_PS_SR2, AG_PS_SR3, AG_PS_SIB_I, AG_PS_SEG1, AG_PS_SEG2, AG_PS_REPNE_WB } = AG_PS_IN1[31:1];

   // [31:25]
   assign D2_OUT2_AG_PS[31:12] = { D2_SIB_EN_AG, D2_DISP_EN_AG, D2_BASE_REG_EN_AG, D2_MUX_SEG_AG,
                                   D2_CMPXCHG_AG, D2_SIB_S_AG,
                                   D2_SR1_SIZE_AG_OUT, D2_SR2_SIZE_AG_OUT,
                                   D2_DR1_SIZE_WB_OUT, D2_DR2_SIZE_WB_OUT,
                                   D2_MEM_SIZE_WB_OUT,
				   D2_NMI_INT_EN_OUT, D2_GEN_PROT_EXC_EN_OUT, D2_PAGE_FAULT_EXC_EN_OUT };
   reg32e$
      u_reg_ag_ps_in2 (CLK, D2_OUT2_AG_PS, AG_PS_IN2, , CLR, PRE, LD_AG);

   assign { AG_PS_DE_SIB_EN_AG, AG_PS_DE_DISP_EN_AG, AG_PS_DE_BASE_REG_EN_AG,
            AG_PS_DE_MUX_SEG_AG, AG_PS_DE_CMPXCHG_AG, AG_PS_DE_SIB_S_AG,
            AG_PS_D2_SR1_SIZE_AG, AG_PS_D2_SR2_SIZE_AG,
            AG_PS_D2_DR1_SIZE_WB, AG_PS_D2_DR2_SIZE_WB,
            AG_PS_D2_MEM_SIZE_WB,
	    AG_PS_NMI_INT_EN, AG_PS_GEN_PROT_EXC_EN, AG_PS_PAGE_FAULT_EXC_EN } = AG_PS_IN2[31:12];

   wire ag_ps_page_fault_exc_exist_bar, ag_ps_v_stage_in;
   inv1$ inv_ag_ps_page_fault_exc_exist (ag_ps_page_fault_exc_exist_bar, AG_PS_PAGE_FAULT_EXC_EXIST);
   and2$ and_ag_ps_v_stage_in (ag_ps_v_stage_in, AG_PS_V, ag_ps_page_fault_exc_exist_bar);

   agen_stage1 u_agen_stage1 (
        CLK, CLR, PRE, ag_ps_v_stage_in, // AG_PS_V,
        // s from pipestage latches
        AG_PS_EIP, AG_PS_CS, AG_PS_CONTROL_STORE, AG_PS_OFFSET, AG_PS_REPNE_WB,
        AG_PS_D2_SR1_NEEDED_AG, AG_PS_D2_SEG1_NEEDED_AG, AG_PS_D2_MM1_NEEDED_AG,
        AG_PS_D2_MEM_RD_ME, AG_PS_D2_MEM_WR_ME,
        AG_PS_D2_ALUK_EX, AG_PS_D2_LD_GPR1_WB, AG_PS_D2_LD_MM_WB,
        AG_PS_SR1, AG_PS_SR2, AG_PS_SR3, AG_PS_SIB_I, AG_PS_SEG1, AG_PS_SEG2,

        AG_PS_D2_SR1_SIZE_AG, AG_PS_D2_SR2_SIZE_AG,
        AG_PS_D2_DR1_SIZE_WB, AG_PS_D2_DR2_SIZE_WB,
        AG_PS_D2_MEM_SIZE_WB,
        
        AG_PS_IMM32, AG_PS_DISP32,
        AG_PS_DE_SIB_EN_AG, AG_PS_DE_DISP_EN_AG, AG_PS_DE_BASE_REG_EN_AG,
        AG_PS_DE_MUX_SEG_AG, AG_PS_DE_CMPXCHG_AG,
        AG_PS_DE_SIB_S_AG,

        // s from register file
        SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
        SEG1_DATA, SEG2_DATA, MM1_DATA, MM2_DATA,

        // s from exception/interrupt logic
        AG_PS_NMI_INT_EN, AG_PS_GEN_PROT_EXC_EN, AG_PS_PAGE_FAULT_EXC_EN,
	AG_PS_PAGE_FAULT_EXC_EXIST,

        // dependency check s
        AG2_PS_V_OUT_AG_IN, AG2_GPR_SCOREBOARD_OUT, AG2_SEG_SCOREBOARD_OUT, AG2_MM_SCOREBOARD_OUT,
        ME_PS_V_OUT_AG_IN, ME_GPR_SCOREBOARD_OUT, ME_SEG_SCOREBOARD_OUT, ME_MM_SCOREBOARD_OUT,
        ME2_PS_V_OUT_AG_IN, ME2_GPR_SCOREBOARD_OUT, ME2_SEG_SCOREBOARD_OUT, ME2_MM_SCOREBOARD_OUT,
        EX_PS_V_OUT_AG_IN, EX_GPR_SCOREBOARD_OUT, EX_SEG_SCOREBOARD_OUT, EX_MM_SCOREBOARD_OUT,
//        1'b0, ME_GPR_SCOREBOARD_OUT, ME_SEG_SCOREBOARD_OUT, ME_MM_SCOREBOARD_OUT,
//        1'b0, EX_GPR_SCOREBOARD_OUT, EX_SEG_SCOREBOARD_OUT, EX_MM_SCOREBOARD_OUT,

//        AG_DRID1, AG_DRID2,
//        V_AG_LD_GPR1, V_AG_LD_GPR2, V_AG_LD_SEG, V_AG_LD_CSEG, V_AG_LD_MM,
//        ME_DRID1, ME_DRID2,
//        V_ME_LD_GPR1, V_ME_LD_GPR2, V_ME_LD_SEG, V_ME_LD_CSEG, V_ME_LD_MM,
//        EX_DRID1, EX_DRID2,
//        V_EX_LD_GPR1, V_EX_LD_GPR2, V_EX_LD_SEG, V_EX_LD_CSEG, V_EX_LD_MM,

        // outputs to register file
        AG_SR1_OUT, AG_SR2_OUT, AG_SR3_OUT, AG_SIB_I_OUT, AG_SEG1_OUT, AG_SEG2_OUT, AG_MM1_OUT, AG_MM2_OUT,

        AG_D2_SR1_SIZE_AG_OUT, AG_D2_SR2_SIZE_AG_OUT,
        AG_D2_SR3_SIZE_AG_OUT, AG_D2_SR4_SIZE_AG_OUT,
        AG_D2_DR1_SIZE_WB_OUT, AG_D2_DR2_SIZE_WB_OUT,
        AG_D2_MEM_SIZE_WB_OUT,

        // outputs to next stage
	AG_EIP_OUT,
        AG_NEIP_OUT, AG_NCS_OUT, AG_CONTROL_STORE_OUT,
        AG_A_OUT, AG_B_OUT, AG_MM_A_OUT, AG_MM_B_OUT, AG_SP_XCHG_DATA_OUT,
        AG_ADD_BASE_DISP_OUT, AG_ADD_SIB_SEG1_OUT, AG_SIB_SI_DATA_OUT,
	AG_SEG1_DATA_OUT, AG_SEG2_DATA_OUT, AG_INTERRUPT_ADDR_OUT,
			      
        AG_D2_ALUK_EX_OUT, AG_DRID1_OUT, AG_DRID2_OUT,
        AG_D2_MEM_RD_ME_OUT, AG_D2_MEM_WR_WB_OUT,
        AG_D2_LD_GPR1_WB_OUT, AG_D2_LD_MM_WB_OUT,

        AG_GPR_SCOREBOARD_OUT,
        AG_SEG_SCOREBOARD_OUT,
        AG_MM_SCOREBOARD_OUT,

        // other outputs
        AG_DEP_STALL_OUT, AG_PAGE_FAULT_EXC_EXIST_OUT, AG_REPNE_WB_OUT,
        AG_EXC_EN_V_OUT
   );

   // Signals to be saved in pipeline latches
   wire [31:0] AG2_PS_EIP; // for segment limit check
   wire [31:0] AG2_PS_NEIP; 
   wire [15:0] AG2_PS_NCS_NC, AG2_PS_NCS;
   wire [127:0] AG2_PS_CONTROL_STORE;
   wire AG2_PS_REPNE_WB;

   wire [31:0] AG2_PS_A, AG2_PS_B;
   wire [63:0] AG2_PS_MM_A, AG2_PS_MM_B;
   wire [31:0] AG2_PS_SP_XCHG_DATA;
   wire [31:0] AG2_PS_ADD_BASE_DISP, AG2_PS_ADD_SIB_SEG1;
   wire [31:0] AG2_PS_SIB_SI_DATA;
   wire [15:0] AG2_PS_SEG1_DATA_NC, AG2_PS_SEG1_DATA;
   wire [15:0] AG2_PS_SEG2_DATA_NC, AG2_PS_SEG2_DATA;
   wire [31:0] AG2_PS_INTERRUPT_ADDR;
   wire [2:0] AG2_PS_SEG1;
			   
   wire [2:0] AG2_PS_D2_ALUK_EX;
   wire [2:0] AG2_PS_DRID1, AG2_PS_DRID2;

   wire AG2_PS_D2_MEM_RD_ME, AG2_PS_D2_MEM_WR_WB;
   wire AG2_PS_D2_LD_GPR1_WB, AG2_PS_D2_LD_MM_WB;

   wire [1:0] AG2_PS_D2_DR1_SIZE_WB, AG2_PS_D2_DR2_SIZE_WB;
   wire [1:0] AG2_PS_D2_MEM_SIZE_WB;

   // EXCEPTION/INTERRUPT STATUS
   wire AG2_PS_PAGE_FAULT_EXC_EXIST, AG2_PS_EXC_EN_V;

   // AG2 outputs		   
   wire [1:0] AG2_D2_DR1_SIZE_WB_OUT, AG2_D2_DR2_SIZE_WB_OUT;
   wire [1:0] AG2_D2_MEM_SIZE_WB_OUT;

   // Signals for next stage latches
   wire AG_AG2_V_OUT;
   wire AG2_PS_V, LD_AG2;
   
   wire [31:0] AG2_NEIP_OUT; 
   wire [15:0] AG2_NCS_OUT;
   wire [127:0] AG2_CONTROL_STORE_OUT;
   wire AG2_REPNE_WB_OUT;

   wire [31:0] AG2_A_OUT, AG2_B_OUT;
   wire [63:0] AG2_MM_A_OUT, AG2_MM_B_OUT;
   wire [31:0] AG2_SP_XCHG_DATA_OUT;
   wire [31:0] AG2_MEM_RD_ADDR_OUT, AG2_MEM_WR_ADDR_OUT;

   wire [2:0] AG2_D2_ALUK_EX_OUT;
   wire [2:0] AG2_DRID1_OUT, AG2_DRID2_OUT;

   wire AG2_D2_MEM_RD_ME_OUT, AG2_D2_MEM_WR_WB_OUT;
   wire AG2_D2_LD_GPR1_WB_OUT, AG2_D2_LD_MM_WB_OUT;

   // Other signals
   wire AG2_SEG_LIMIT_EXC_EXIST_OUT, AG2_PAGE_FAULT_EXC_EXIST_OUT;

   // TODO AG2_V = !REG_DEP_STALL
   wire ag_dep_stall_out_bar, and_flush_ag2_v_out;

   inv1$ inv_dep_stall (ag_dep_stall_out_bar, AG_DEP_STALL_OUT);

//   nor4$ nor_me_v (nor_me_v_out, WB_EXC_V_OUT, wb_repne_terminate_all, INTERRUPT_SIGNAL);
   and2$ and_flush_ag2_v (and_flush_ag2_v_out, WB_FLUSH_PIPELINE_BAR, ag_dep_stall_out_bar);
   and2$ and_ag2_v (AG_AG2_V_OUT, AG_PS_V, and_flush_ag2_v_out);

   wire ME_STALL_OUT_LD_AG2_IN;
//   and2$ and_ag2_v (AG_AG2_V_OUT, AG_PS_V, ag_dep_stall_out_bar); 
   // assign AG_AG2_V_OUT = 1'b1;
   // LD_AG2 = !MEM_DEP_STALL && !MEM_RD_STALL && !MEM_WR_STALL
   // assign LD_AG2 = 1'b1;
   assign LD_AG2 = ME_STALL_OUT_LD_AG2_IN; 

   // FOR REG DEPENDENCY CHECKS
   wire [63:0] ag2_ps_save_sb, AG2_PS_SCOREBOARDS;
   assign ag2_ps_save_sb[63:26] = { AG_GPR_SCOREBOARD_OUT, AG_SEG_SCOREBOARD_OUT, AG_MM_SCOREBOARD_OUT };
   assign { AG2_GPR_SCOREBOARD_OUT, AG2_SEG_SCOREBOARD_OUT, AG2_MM_SCOREBOARD_OUT } = AG2_PS_SCOREBOARDS[63:26];

   reg64e$
     u_reg_ag2_ps_sb (CLK, ag2_ps_save_sb, AG2_PS_SCOREBOARDS, , CLR, PRE, LD_AG2);
   //==========================
   
   reg32e$
      u_reg_ag2_ps_eip (CLK, AG_EIP_OUT, AG2_PS_EIP, , CLR, PRE, LD_AG2),
      u_reg_ag2_ps_neip (CLK, AG_NEIP_OUT, AG2_PS_NEIP, , CLR, PRE, LD_AG2),
      u_reg_ag2_ps_cs (CLK, {16'b0, AG_NCS_OUT}, {AG2_PS_NCS_NC, AG2_PS_NCS}, , CLR, PRE, LD_AG2);

   reg64e$
     u_reg_ag2_ps_control_store0 (CLK, AG_CONTROL_STORE_OUT[127:64], AG2_PS_CONTROL_STORE[127:64], , CLR, PRE, LD_AG2),
     u_reg_ag2_ps_control_store1 (CLK, AG_CONTROL_STORE_OUT[63:0], AG2_PS_CONTROL_STORE[63:0], , CLR, PRE, LD_AG2);

   reg32e$
     u_reg_ag2_ps_a (CLK, AG_A_OUT, AG2_PS_A, , CLR, PRE, LD_AG2),
     u_reg_ag2_ps_b (CLK, AG_B_OUT, AG2_PS_B, , CLR, PRE, LD_AG2);
   reg64e$
     u_reg_ag2_ps_mm_a (CLK, AG_MM_A_OUT, AG2_PS_MM_A, , CLR, PRE, LD_AG2),
     u_reg_ag2_ps_mm_b (CLK, AG_MM_B_OUT, AG2_PS_MM_B, , CLR, PRE, LD_AG2);

   reg32e$
     u_reg_ag2_ps_sp_xchg_data (CLK, AG_SP_XCHG_DATA_OUT, AG2_PS_SP_XCHG_DATA, , CLR, PRE, LD_AG2),
     u_reg_ag2_ps_add_base_disp (CLK, AG_ADD_BASE_DISP_OUT, AG2_PS_ADD_BASE_DISP, , CLR, PRE, LD_AG2),
     u_reg_ag2_ps_add_sib_seg1 (CLK, AG_ADD_SIB_SEG1_OUT, AG2_PS_ADD_SIB_SEG1, , CLR, PRE, LD_AG2),
     u_reg_ag2_ps_sib_si_data (CLK, AG_SIB_SI_DATA_OUT, AG2_PS_SIB_SI_DATA, , CLR, PRE, LD_AG2),
     u_reg_ag2_ps_seg1_data (CLK, {16'b0, AG_SEG1_DATA_OUT}, {AG2_PS_SEG1_DATA_NC, AG2_PS_SEG1_DATA}, , CLR, PRE, LD_AG2),
     u_reg_ag2_ps_seg2_data (CLK, {16'b0, AG_SEG2_DATA_OUT}, {AG2_PS_SEG2_DATA_NC, AG2_PS_SEG2_DATA}, , CLR, PRE, LD_AG2),
     u_reg_ag2_ps_int_addr (CLK, AG_INTERRUPT_ADDR_OUT, AG2_PS_INTERRUPT_ADDR, , CLR, PRE, LD_AG2);

   wire [31:0] AG_OUT1_AG2_PS, AG2_PS_IN1;
   assign AG_OUT1_AG2_PS[31:6] = { AG_AG2_V_OUT, AG_EXC_EN_V_OUT,
                                AG_SEG1_OUT, AG_D2_ALUK_EX_OUT, AG_DRID1_OUT, AG_DRID2_OUT,
                                AG_D2_MEM_RD_ME_OUT, AG_D2_MEM_WR_WB_OUT, AG_D2_LD_GPR1_WB_OUT,
                                AG_D2_LD_MM_WB_OUT, AG_D2_DR1_SIZE_WB_OUT, AG_D2_DR2_SIZE_WB_OUT,
                                AG_D2_MEM_SIZE_WB_OUT, AG_PAGE_FAULT_EXC_EXIST_OUT, AG_REPNE_WB_OUT };
   assign { AG2_PS_V, AG2_PS_EXC_EN_V, AG2_PS_SEG1, AG2_PS_D2_ALUK_EX, AG2_PS_DRID1, AG2_PS_DRID2,
            AG2_PS_D2_MEM_RD_ME, AG2_PS_D2_MEM_WR_WB, AG2_PS_D2_LD_GPR1_WB,
            AG2_PS_D2_LD_MM_WB, AG2_PS_D2_DR1_SIZE_WB, AG2_PS_D2_DR2_SIZE_WB,
            AG2_PS_D2_MEM_SIZE_WB, AG2_PS_PAGE_FAULT_EXC_EXIST, AG2_PS_REPNE_WB } = AG2_PS_IN1[31:6];
   reg32e$ u_reg_ag2_ps_in1 (CLK, AG_OUT1_AG2_PS, AG2_PS_IN1, , CLR, PRE, LD_AG2);

   and2$ and_ag2_exc_en_v (AG2_EXC_EN_V_OUT, AG2_PS_V, AG2_PS_EXC_EN_V);

   // TODO forwarded?
   wire EFLAGS_DF = EFLAGSDOUT[10];

   wire ag2_ps_page_fault_exc_exist_bar, ag2_ps_v_stage_in;
   inv1$ inv_ag2_ps_page_fault_exc_exist (ag2_ps_page_fault_exc_exist_bar, AG2_PS_PAGE_FAULT_EXC_EXIST);
   and2$ and_ag2_ps_v_stage_in (ag2_ps_v_stage_in, AG2_PS_V, ag2_ps_page_fault_exc_exist_bar);

   // agen_stage1 dependency check input
   assign AG2_PS_V_OUT_AG_IN = ag2_ps_v_stage_in;
   //==================================
   
   agen_stage2 u_agen_stage2 (
      CLK, CLR, PRE, ag2_ps_v_stage_in,

      AG2_PS_EIP, AG2_PS_NEIP, AG2_PS_NCS,
      AG2_PS_CONTROL_STORE,

      AG2_PS_A, AG2_PS_B,
      AG2_PS_MM_A, AG2_PS_MM_B,
      AG2_PS_SP_XCHG_DATA,
      AG2_PS_ADD_BASE_DISP, AG2_PS_ADD_SIB_SEG1,
      AG2_PS_SIB_SI_DATA, AG2_PS_SEG1_DATA, AG2_PS_SEG2_DATA,
      AG2_PS_INTERRUPT_ADDR,
      AG2_PS_SEG1,

      AG2_PS_D2_ALUK_EX, AG2_PS_DRID1, AG2_PS_DRID2,

      AG2_PS_D2_MEM_RD_ME, AG2_PS_D2_MEM_WR_WB,
      AG2_PS_D2_LD_GPR1_WB, AG2_PS_D2_LD_MM_WB,

      AG2_PS_D2_DR1_SIZE_WB, AG2_PS_D2_DR2_SIZE_WB,
      AG2_PS_D2_MEM_SIZE_WB, AG2_PS_REPNE_WB, EFLAGS_DF,

      AG2_PS_PAGE_FAULT_EXC_EXIST,

      // Signals for next stage latches
      AG2_D2_DR1_SIZE_WB_OUT, AG2_D2_DR2_SIZE_WB_OUT,
      AG2_D2_MEM_SIZE_WB_OUT,

      AG2_NEIP_OUT, 
      AG2_NCS_OUT,
      AG2_CONTROL_STORE_OUT,

      AG2_A_OUT, AG2_B_OUT,
      AG2_MM_A_OUT, AG2_MM_B_OUT,
      AG2_SP_XCHG_DATA_OUT,
      AG2_MEM_RD_ADDR_OUT, AG2_MEM_WR_ADDR_OUT,

      AG2_D2_ALUK_EX_OUT,
      AG2_DRID1_OUT, AG2_DRID2_OUT,

      AG2_D2_MEM_RD_ME_OUT, AG2_D2_MEM_WR_WB_OUT,
      AG2_D2_LD_GPR1_WB_OUT, AG2_D2_LD_MM_WB_OUT,

      // Other signals
      AG2_SEG_LIMIT_EXC_EXIST_OUT, AG2_PAGE_FAULT_EXC_EXIST_OUT, AG2_REPNE_WB_OUT
   );
    
   wire ME_PS_V;
   wire [31:0] ME_PS_NEIP, ME_PS_NEIP_NOT_TAKEN;
   wire [15:0] ME_PS_NCS, ME_PS_NCS_NC;
   wire [127:0] ME_PS_CONTROL_STORE;

   wire [31:0] ME_PS_A, ME_PS_B;
   wire [63:0] ME_PS_MM_A, ME_PS_MM_B;
   wire [31:0] ME_PS_SP_XCHG_DATA;

   wire [31:0] ME_PS_MEM_RD_ADDR, ME_PS_MEM_WR_ADDR;
   wire [1:0] ME_PS_D2_DR1_SIZE_WB, ME_PS_D2_DR2_SIZE_WB;
   wire [1:0] ME_PS_D2_MEM_SIZE_WB;
   wire ME_PS_D2_REPNE_WB;

   wire [2:0] ME_PS_D2_ALUK_EX;
   wire [2:0] ME_PS_DRID1, ME_PS_DRID2;

   wire ME_PS_D2_MEM_RD_ME, ME_PS_D2_MEM_WR_WB, ME_PS_D2_LD_GPR1_WB, ME_PS_D2_LD_MM_WB;

   // interrupts/exceptions
   wire ME_PS_GPROT_EXC_EXIST, ME_PS_PAGE_FAULT_EXC_EXIST, ME_PS_EXC_EN_V;

   wire [31:0] ME_MEM_WR_ADDR_OUT;
   wire [1:0] ME_D2_MEM_SIZE_WB_OUT;
   wire ME_D2_MEM_WR_WB_OUT;

   wire ME_RD_ADDR1_V_OUT, ME_RD_ADDR2_V_OUT, ME_WR_ADDR1_V_OUT, ME_WR_ADDR2_V_OUT;
   wire [31:0] ME_RA_RD_ADDR1_OUT, ME_RA_RD_ADDR2_OUT, ME_RA_WR_ADDR1_OUT, ME_RA_WR_ADDR2_OUT;
   wire [3:0]  ME_RA_RD_SIZE1_OUT, ME_RA_RD_SIZE2_OUT, ME_RA_WR_SIZE1_OUT, ME_RA_WR_SIZE2_OUT;

   wire ME_PAGE_FAULT_EXC_OUT, ME_GPROT_EXC_OUT; //ME_MEM_DEP_STALL_OUT;
   
   wire [31:0] AG2_OUT1_ME_PS, ME_PS_IN1;

   wire LD_ME, AG2_ME_V_OUT;

//   nor4$ nor_me_v (nor_me_v_out, WB_EXC_V_OUT, wb_repne_terminate_all, INTERRUPT_SIGNAL);
   and2$ and_me_v (AG2_ME_V_OUT, AG2_PS_V, WB_FLUSH_PIPELINE_BAR);
   // assign AG2_ME_V_OUT = AG2_ME_V_OUT;

   // LD_ME = !ME_MEM_DEP_STALL_OUT && !ME2_STALL && !WB_STALL
   // TODO ME_V = AG2_V
   // assign LD_ME = 1'b1;
   nor3$ nor_ld_me (LD_ME, LSU_OUT_RD_STALL, LSU_OUT_WR_STALL, ME_MEM_DEP_STALL_OUT);
   assign ME_STALL_OUT_LD_AG2_IN = LD_ME;

   wire [63:0] me_ps_save_sb, ME_PS_SCOREBOARDS;
   assign me_ps_save_sb[63:26] = { AG2_GPR_SCOREBOARD_OUT, AG2_SEG_SCOREBOARD_OUT, AG2_MM_SCOREBOARD_OUT };
   assign { ME_GPR_SCOREBOARD_OUT, ME_SEG_SCOREBOARD_OUT, ME_MM_SCOREBOARD_OUT } = ME_PS_SCOREBOARDS[63:26];

   reg64e$
     u_reg_me_ps_sb (CLK, me_ps_save_sb, ME_PS_SCOREBOARDS, , CLR, PRE, LD_ME);

   reg32e$
     u_reg_me_ps_neip_not_taken (CLK, AG2_PS_EIP, ME_PS_NEIP_NOT_TAKEN, , CLR, PRE, LD_ME),
     u_reg_me_ps_neip (CLK, AG2_NEIP_OUT, ME_PS_NEIP, , CLR, PRE, LD_ME),
     u_reg_me_ps_cs (CLK, {16'b0, AG2_NCS_OUT}, {ME_PS_NCS_NC, ME_PS_NCS}, , CLR, PRE, LD_ME);

   reg64e$
     u_reg_me_ps_control_store0 (CLK, AG2_CONTROL_STORE_OUT[127:64], ME_PS_CONTROL_STORE[127:64], , CLR, PRE, LD_ME),
     u_reg_me_ps_control_store1 (CLK, AG2_CONTROL_STORE_OUT[63:0], ME_PS_CONTROL_STORE[63:0], , CLR, PRE, LD_ME);

   reg32e$
     u_reg_me_ps_a (CLK, AG2_A_OUT, ME_PS_A, , CLR, PRE, LD_ME),
     u_reg_me_ps_b (CLK, AG2_B_OUT, ME_PS_B, , CLR, PRE, LD_ME);

   reg64e$
     u_reg_me_ps_mm_a (CLK, AG2_MM_A_OUT, ME_PS_MM_A, , CLR, PRE, LD_ME),
     u_reg_me_ps_mm_b (CLK, AG2_MM_B_OUT, ME_PS_MM_B, , CLR, PRE, LD_ME);

   reg32e$
     u_reg_me_ps_sp_xchg_data (CLK, AG2_SP_XCHG_DATA_OUT, ME_PS_SP_XCHG_DATA, , CLR, PRE, LD_ME),
     u_reg_me_mem_rd_addr (CLK, AG2_MEM_RD_ADDR_OUT, ME_PS_MEM_RD_ADDR, , CLR, PRE, LD_ME),
     u_reg_me_mem_wr_addr (CLK, AG2_MEM_WR_ADDR_OUT, ME_PS_MEM_WR_ADDR, , CLR, PRE, LD_ME);

   assign AG2_OUT1_ME_PS[31:8] = { AG2_ME_V_OUT,
          AG2_SEG_LIMIT_EXC_EXIST_OUT, AG2_PAGE_FAULT_EXC_EXIST_OUT, AG2_PS_EXC_EN_V,
          AG2_D2_ALUK_EX_OUT, AG2_DRID1_OUT, AG2_DRID2_OUT, AG2_D2_MEM_RD_ME_OUT, AG2_D2_MEM_WR_WB_OUT,
	  AG2_D2_LD_GPR1_WB_OUT, AG2_D2_LD_MM_WB_OUT,
          AG2_D2_DR1_SIZE_WB_OUT, AG2_D2_DR2_SIZE_WB_OUT,
          AG2_D2_MEM_SIZE_WB_OUT, AG2_REPNE_WB_OUT }; 

   reg32e$
     u_reg_me_ps_in1 (CLK, AG2_OUT1_ME_PS, ME_PS_IN1, , CLR, PRE, LD_ME);

   assign { ME_PS_V, ME_PS_GPROT_EXC_EXIST, ME_PS_PAGE_FAULT_EXC_EXIST, ME_PS_EXC_EN_V,
            ME_PS_D2_ALUK_EX, ME_PS_DRID1, ME_PS_DRID2, ME_PS_D2_MEM_RD_ME, ME_PS_D2_MEM_WR_WB,
            ME_PS_D2_LD_GPR1_WB, ME_PS_D2_LD_MM_WB,
            ME_PS_D2_DR1_SIZE_WB, ME_PS_D2_DR2_SIZE_WB,
            ME_PS_D2_MEM_SIZE_WB, ME_PS_D2_REPNE_WB } = ME_PS_IN1[31:8];

   wire nor_me_exc_exist_out, me_ps_v_stage_in;
   nor2$ nor_me_exc_exist (nor_me_exc_exist_out, ME_PS_GPROT_EXC_EXIST, ME_PS_PAGE_FAULT_EXC_EXIST);
   and2$ and_me_ps_v_stage_in (me_ps_v_stage_in, ME_PS_V, nor_me_exc_exist_out);

   // agen_stage1 dependency check input
   assign ME_PS_V_OUT_AG_IN = me_ps_v_stage_in;
   //==================================
   
   wire ME2_V_ME_IN, ME2_WR_ADDR1_V_ME_IN, ME2_WR_ADDR2_V_ME_IN,
	EX_V_ME_IN, EX_WR_ADDR1_V_ME_IN, EX_WR_ADDR2_V_ME_IN;
   wire [31:0] ME2_WR_ADDR1_ME_IN, ME2_WR_ADDR2_ME_IN,
	       EX_WR_ADDR1_ME_IN, EX_WR_ADDR2_ME_IN;
   wire [3:0] ME2_WR_SIZE1_ME_IN, ME2_WR_SIZE2_ME_IN,
	      EX_WR_SIZE1_ME_IN, EX_WR_SIZE2_ME_IN;
   
   memory_stage1 u_memory_stage1 (
      CLK, CLR, PRE, me_ps_v_stage_in, // ME_PS_V,

      // inputs from previous stage
      ME_PS_MEM_RD_ADDR, ME_PS_MEM_WR_ADDR,
      ME_PS_D2_MEM_SIZE_WB,

      ME_PS_D2_MEM_RD_ME, ME_PS_D2_MEM_WR_WB,

      // inputs for dependency check
      ME2_V_ME_IN,
      ME2_WR_ADDR1_V_ME_IN, ME2_WR_ADDR1_ME_IN, ME2_WR_SIZE1_ME_IN,
      ME2_WR_ADDR2_V_ME_IN, ME2_WR_ADDR2_ME_IN, ME2_WR_SIZE2_ME_IN,

      EX_V_ME_IN,
      EX_WR_ADDR1_V_ME_IN, EX_WR_ADDR1_ME_IN, EX_WR_SIZE1_ME_IN,
      EX_WR_ADDR2_V_ME_IN, EX_WR_ADDR2_ME_IN, EX_WR_SIZE2_ME_IN,

      // outputs
      ME_MEM_WR_ADDR_OUT, ME_D2_MEM_SIZE_WB_OUT,
      ME_D2_MEM_WR_WB_OUT,

      ME_RD_ADDR1_V_OUT, ME_RA_RD_ADDR1_OUT, ME_RA_RD_SIZE1_OUT,
      ME_RD_ADDR2_V_OUT, ME_RA_RD_ADDR2_OUT, ME_RA_RD_SIZE2_OUT,
			  
      ME_WR_ADDR1_V_OUT, ME_RA_WR_ADDR1_OUT, ME_RA_WR_SIZE1_OUT,
      ME_WR_ADDR2_V_OUT, ME_RA_WR_ADDR2_OUT, ME_RA_WR_SIZE2_OUT,
				  
      ME_PAGE_FAULT_EXC_OUT, ME_GPROT_EXC_OUT, ME_MEM_DEP_STALL_OUT
   );

   wire ME_PAGE_FAULT_EXC_EXIST_OUT, ME_GPROT_EXC_EXIST_OUT;
   or2$ or0_me_page_fault (ME_PAGE_FAULT_EXC_EXIST_OUT, ME_PAGE_FAULT_EXC_OUT, ME_PS_PAGE_FAULT_EXC_EXIST);
   or2$ or0_me_gprot_exc (ME_GPROT_EXC_EXIST_OUT, ME_GPROT_EXC_OUT, ME_PS_GPROT_EXC_EXIST);
   and2$ and0_me_exc_en (ME_EXC_EN_V_OUT, ME_PS_V, ME_PS_EXC_EN_V);

   wire ME2_PS_V;
   wire [31:0] ME2_PS_NEIP, ME2_PS_NEIP_NOT_TAKEN;
   wire [15:0] ME2_PS_NCS, ME2_PS_NCS_NC;
   wire [127:0] ME2_PS_CONTROL_STORE;

   wire [31:0] ME2_PS_A, ME2_PS_B;
   wire [63:0] ME2_PS_MM_A, ME2_PS_MM_B;
   wire [31:0] ME2_PS_SP_XCHG_DATA;

   wire [31:0] ME2_PS_MEM_RD_ADDR, ME2_PS_MEM_WR_ADDR;
   wire [1:0] ME2_PS_D2_DR1_SIZE_WB, ME2_PS_D2_DR2_SIZE_WB;
   wire [1:0] ME2_PS_D2_MEM_SIZE_WB;

   wire [2:0] ME2_PS_D2_ALUK_EX;
   wire [2:0] ME2_PS_DRID1, ME2_PS_DRID2;

   wire ME2_PS_D2_MEM_RD_ME, ME2_PS_D2_MEM_WR_WB, ME2_PS_D2_LD_GPR1_WB, ME2_PS_D2_LD_MM_WB;

   // Signals not from latches
   wire [63:0] DCACHE_DATA;
   wire DCACHE_READY;

   wire ME2_DCACHE_EN;

   wire [31:0] ME2_NEIP_OUT;
   wire [15:0] ME2_NCS_OUT;
   wire [127:0] ME2_CONTROL_STORE_OUT;

   wire [31:0] ME2_A_OUT, ME2_B_OUT;
   wire [63:0] ME2_MM_A_OUT, ME2_MM_B_OUT;
   wire [31:0] ME2_SP_XCHG_DATA_OUT;

   wire [31:0] ME2_MEM_RD_ADDR_OUT, ME2_MEM_WR_ADDR_OUT;
   wire [1:0] ME2_D2_DR1_SIZE_WB_OUT, ME2_D2_DR2_SIZE_WB_OUT;
   wire [1:0] ME2_D2_MEM_SIZE_WB_OUT;
   wire ME2_PS_D2_REPNE_WB;

   wire [2:0] ME2_D2_ALUK_EX_OUT;
   wire [2:0] ME2_DRID1_OUT, ME2_DRID2_OUT;

   wire ME2_D2_MEM_WR_WB_OUT, ME2_D2_LD_GPR1_WB_OUT, ME2_D2_LD_MM_WB_OUT;

   wire [31:0] ME_OUT1_ME2_PS, ME2_PS_IN1;

   wire LD_ME2, ME_ME2_V_OUT;
   wire nor_me2_v_out;
//   wire me_mem_dep_stall_out_bar;

   nor4$ nor_me2_v (nor_me2_v_out, WB_EXC_V_OUT, wb_repne_terminate_all, INTERRUPT_SIGNAL, ME_MEM_DEP_STALL_OUT);
//   inv1$ inv_me2_dep_stall (me_mem_dep_stall_out_bar, ME_MEM_DEP_STALL_OUT);
   and2$ and_me_me2_v (ME_ME2_V_OUT, ME_PS_V, nor_me2_v_out);

   // LD_ME2 = !ME2_STALL && !WB_STALL
   // TODO
   //assign LD_ME2 = 1'b1;
   nor2$ nor_ld_me2 (LD_ME2, LSU_OUT_RD_STALL, LSU_OUT_WR_STALL);

   //= FOR DEPENDENCY CHECKS =======//
   wire [63:0] me2_ps_save_sb, ME2_PS_SCOREBOARDS;
   
   assign me2_ps_save_sb[63:26] = { ME_GPR_SCOREBOARD_OUT, ME_SEG_SCOREBOARD_OUT, ME_MM_SCOREBOARD_OUT };
   assign { ME2_GPR_SCOREBOARD_OUT, ME2_SEG_SCOREBOARD_OUT, ME2_MM_SCOREBOARD_OUT } = ME2_PS_SCOREBOARDS[63:26];
   
   reg64e$
     u_reg_me2_ps_sb (CLK, me2_ps_save_sb, ME2_PS_SCOREBOARDS, , CLR, PRE, LD_ME2);

   wire [63:0] me2_ps_save_rd_ra, me2_ps_save_wr_ra, ME2_PS_RD_RA, ME2_PS_WR_RA;
   wire [31:0] ME2_PS_RA_RD_ADDR1, ME2_PS_RA_RD_ADDR2,
	       ME2_PS_RA_WR_ADDR1, ME2_PS_RA_WR_ADDR2;
   
   assign me2_ps_save_rd_ra = {ME_RA_RD_ADDR1_OUT, ME_RA_RD_ADDR2_OUT};
   assign me2_ps_save_wr_ra = {ME_RA_WR_ADDR1_OUT, ME_RA_WR_ADDR2_OUT};
   assign {ME2_PS_RA_RD_ADDR1, ME2_PS_RA_RD_ADDR2} = ME2_PS_RD_RA;
   assign {ME2_PS_RA_WR_ADDR1, ME2_PS_RA_WR_ADDR2} = ME2_PS_WR_RA;
   
   reg64e$
     u_reg_me2_ps_save_rd_ra (CLK, me2_ps_save_rd_ra, ME2_PS_RD_RA, , CLR, PRE, LD_ME2),
     u_reg_me2_ps_save_wr_ra (CLK, me2_ps_save_wr_ra, ME2_PS_WR_RA, , CLR, PRE, LD_ME2);
   
   wire [31:0] me2_ps_save_mem, ME2_PS_SAVE_MEM;
   wire ME2_PS_RD_ADDR1_V, ME2_PS_RD_ADDR2_V, ME2_PS_WR_ADDR1_V, ME2_PS_WR_ADDR2_V;
   wire [3:0] ME2_PS_RA_RD_SIZE1, ME2_PS_RA_RD_SIZE2, ME2_PS_RA_WR_SIZE1, ME2_PS_RA_WR_SIZE2;
   wire ME2_PS_PAGE_FAULT_EXC_EXIST, ME2_PS_GPROT_EXC_EXIST, ME2_PS_EXC_EN_V;
   
   assign me2_ps_save_mem[31:9] = {ME_RD_ADDR1_V_OUT, ME_RA_RD_SIZE1_OUT, ME_RD_ADDR2_V_OUT, ME_RA_RD_SIZE2_OUT,
                                    ME_WR_ADDR1_V_OUT, ME_RA_WR_SIZE1_OUT, ME_WR_ADDR2_V_OUT, ME_RA_WR_SIZE2_OUT,
                                    ME_PAGE_FAULT_EXC_EXIST_OUT, ME_GPROT_EXC_EXIST_OUT, ME_EXC_EN_V_OUT};
   assign {ME2_PS_RD_ADDR1_V, ME2_PS_RA_RD_SIZE1, ME2_PS_RD_ADDR2_V, ME2_PS_RA_RD_SIZE2,
           ME2_PS_WR_ADDR1_V, ME2_PS_RA_WR_SIZE1, ME2_PS_WR_ADDR2_V, ME2_PS_RA_WR_SIZE2,
           ME2_PS_PAGE_FAULT_EXC_EXIST, ME2_PS_GPROT_EXC_EXIST, ME2_PS_EXC_EN_V} = ME2_PS_SAVE_MEM[31:9];

   and2$ and_me2_exc_en (ME2_EXC_EN_V_OUT, ME2_PS_V, ME2_PS_EXC_EN_V);

   reg32e$ u_reg_me2_ps_save_mem (CLK, me2_ps_save_mem, ME2_PS_SAVE_MEM, , CLR, PRE, LD_ME2);

   wire nor_me2_exc_exist_out, me2_ps_v_stage_in;
   nor2$ nor_me2_exc_exist (nor_me2_exc_exist_out, ME2_PS_PAGE_FAULT_EXC_EXIST, ME2_PS_GPROT_EXC_EXIST);
   and2$ and_me2_v_stage_in (me2_v_stage_in, ME2_PS_V, nor_me2_exc_exist_out);

   assign ME2_V_ME_IN = me2_ps_v_stage_in;
   assign ME2_WR_ADDR1_V_ME_IN = ME2_PS_WR_ADDR1_V;
   assign ME2_WR_ADDR1_ME_IN = ME2_PS_RA_WR_ADDR1;
   assign ME2_WR_SIZE1_ME_IN = ME2_PS_RA_WR_SIZE1;
   assign ME2_WR_ADDR2_V_ME_IN = ME2_PS_WR_ADDR2_V;
   assign ME2_WR_ADDR2_ME_IN = ME2_PS_RA_WR_ADDR2;
   assign ME2_WR_SIZE2_ME_IN = ME2_PS_RA_WR_SIZE2;

   // LSU Inputs
   assign ME2_RD_ADDR1_V_LSU_IN = ME2_PS_RD_ADDR1_V;
   assign ME2_RD_ADDR1_LSU_IN = ME2_PS_RA_RD_ADDR1;
   assign ME2_RD_SIZE1_LSU_IN = ME2_PS_RA_RD_SIZE1;
   assign ME2_RD_ADDR2_V_LSU_IN = ME2_PS_WR_ADDR1_V;
   assign ME2_RD_ADDR2_LSU_IN = ME2_PS_RA_RD_ADDR2;
   assign ME2_RD_SIZE2_LSU_IN = ME2_PS_RA_RD_SIZE2;

   assign ME2_V_LSU_IN = me2_ps_v_stage_in;
   assign ME2_MEM_RD_LSU_IN = ME2_PS_D2_MEM_RD_ME;
   //==================================================================================//
   
   reg32e$
     u_reg_me2_ps_neip_not_taken (CLK, ME_PS_NEIP_NOT_TAKEN, ME2_PS_NEIP_NOT_TAKEN, , CLR, PRE, LD_ME2),
     u_reg_me2_ps_neip (CLK, ME_PS_NEIP, ME2_PS_NEIP, , CLR, PRE, LD_ME2),
     u_reg_me2_ps_cs (CLK, {16'b0, ME_PS_NCS}, {ME2_PS_NCS_NC, ME2_PS_NCS}, , CLR, PRE, LD_ME2);

   reg64e$
     u_reg_me2_ps_control_store0 (CLK, ME_PS_CONTROL_STORE[127:64], ME2_PS_CONTROL_STORE[127:64], , CLR, PRE, LD_ME2),
     u_reg_me2_ps_control_store1 (CLK, ME_PS_CONTROL_STORE[63:0], ME2_PS_CONTROL_STORE[63:0], , CLR, PRE, LD_ME2);

   reg32e$
     u_reg_me2_ps_a (CLK, ME_PS_A, ME2_PS_A, , CLR, PRE, LD_ME2),
     u_reg_me2_ps_b (CLK, ME_PS_B, ME2_PS_B, , CLR, PRE, LD_ME2);

   reg64e$
     u_reg_me2_ps_mm_a (CLK, ME_PS_MM_A, ME2_PS_MM_A, , CLR, PRE, LD_ME2),
     u_reg_me2_ps_mm_b (CLK, ME_PS_MM_B, ME2_PS_MM_B, , CLR, PRE, LD_ME2);

   reg32e$
     u_reg_me2_ps_sp_xchg_data (CLK, ME_PS_SP_XCHG_DATA, ME2_PS_SP_XCHG_DATA, , CLR, PRE, LD_ME2),
     u_reg_me2_mem_rd_addr (CLK, ME_PS_MEM_RD_ADDR, ME2_PS_MEM_RD_ADDR, , CLR, PRE, LD_ME2),
     u_reg_me2_mem_wr_addr (CLK, ME_PS_MEM_WR_ADDR, ME2_PS_MEM_WR_ADDR, , CLR, PRE, LD_ME2);

   assign ME_OUT1_ME2_PS[31:11] = { ME_ME2_V_OUT,
          ME_PS_D2_ALUK_EX, ME_PS_DRID1, ME_PS_DRID2, ME_PS_D2_MEM_RD_ME, ME_PS_D2_MEM_WR_WB,
	  ME_PS_D2_LD_GPR1_WB, ME_PS_D2_LD_MM_WB,
          ME_PS_D2_DR1_SIZE_WB, ME_PS_D2_DR2_SIZE_WB,
          ME_PS_D2_MEM_SIZE_WB, ME_PS_D2_REPNE_WB }; 

   reg32e$
     u_reg_me2_ps_in1 (CLK, ME_OUT1_ME2_PS, ME2_PS_IN1, , CLR, PRE, LD_ME2);

   assign { ME2_PS_V,
            ME2_PS_D2_ALUK_EX, ME2_PS_DRID1, ME2_PS_DRID2, ME2_PS_D2_MEM_RD_ME, ME2_PS_D2_MEM_WR_WB,
            ME2_PS_D2_LD_GPR1_WB, ME2_PS_D2_LD_MM_WB,
            ME2_PS_D2_DR1_SIZE_WB, ME2_PS_D2_DR2_SIZE_WB,
            ME2_PS_D2_MEM_SIZE_WB, ME2_PS_D2_REPNE_WB } = ME2_PS_IN1[31:11];

   // agen_stage1 dependency check inputs
   assign ME2_PS_V_OUT_AG_IN = me2_ps_v_stage_in;
   //===================================
   
    //******************************************************************************//
    //*
    //*                                MEMORY STAGE
    //*
    //*******************************************************************************//

   memory_stage2 u_memory_stage2 (
        CLK, CLR, PRE, me2_ps_v_stage_in,

        ME2_PS_NEIP,
        ME2_PS_NCS,
        ME2_PS_CONTROL_STORE,

        ME2_PS_A, ME2_PS_B,
        ME2_PS_MM_A, ME2_PS_MM_B,
        ME2_PS_SP_XCHG_DATA,

        ME2_PS_MEM_RD_ADDR, ME2_PS_MEM_WR_ADDR,
        ME2_PS_D2_DR1_SIZE_WB, ME2_PS_D2_DR2_SIZE_WB,
        ME2_PS_D2_MEM_SIZE_WB,

        ME2_PS_D2_ALUK_EX,
        ME2_PS_DRID1, ME2_PS_DRID2,

        ME2_PS_D2_MEM_RD_ME, ME2_PS_D2_MEM_WR_WB, ME2_PS_D2_LD_GPR1_WB, ME2_PS_D2_LD_MM_WB,

        DCACHE_DATA, //debug only
        //LSU_OUT_RD_DATA,
        DCACHE_READY,

        // output
        ME2_DCACHE_EN,

        // outputs to next stage latches
        ME2_NEIP_OUT,
        ME2_NCS_OUT,
        ME2_CONTROL_STORE_OUT,

        ME2_A_OUT, ME2_B_OUT,
        ME2_MM_A_OUT, ME2_MM_B_OUT,
        ME2_SP_XCHG_DATA_OUT,

        ME2_MEM_RD_ADDR_OUT, ME2_MEM_WR_ADDR_OUT,
        ME2_D2_DR1_SIZE_WB_OUT, ME2_D2_DR2_SIZE_WB_OUT,
        ME2_D2_MEM_SIZE_WB_OUT,

        ME2_D2_ALUK_EX_OUT,
        ME2_DRID1_OUT, ME2_DRID2_OUT,

        ME2_D2_MEM_WR_WB_OUT, ME2_D2_LD_GPR1_WB_OUT, ME2_D2_LD_MM_WB_OUT
    );
   
    //register between ME and EX
    //reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);
    //reg32e$ REG_DEST_COM(CLK, {{31{1'b0}},REG_DEST_COM_IN}, D_REG_DEST, D_3, CLR, PRE, EN);
    //EX_V_next = ME2_PS_V && !MEM_RD_STALL && !MEM_DEP_STALL
    //LD_EX = !MEM_WR_STALL

   wire EX_V;
   
   // FOR DEPENDENCY CHECKS Nelson added
   // LD_EX = !MEM_WR_STALL
   wire LD_EX;
   //assign LD_EX = 1'b1;
   assign LD_EX = LSU_OUT_WR_STALL_BAR;

   wire [63:0] ex_ps_save_sb, EX_PS_SCOREBOARDS;
   assign ex_ps_save_sb[63:26] = { ME2_GPR_SCOREBOARD_OUT, ME2_SEG_SCOREBOARD_OUT, ME2_MM_SCOREBOARD_OUT };
   assign { EX_GPR_SCOREBOARD_OUT, EX_SEG_SCOREBOARD_OUT, EX_MM_SCOREBOARD_OUT } = EX_PS_SCOREBOARDS[63:26];

   reg64e$ u_reg_ex_ps_sb (CLK, ex_ps_save_sb, EX_PS_SCOREBOARDS, , CLR, PRE, LD_EX);

   wire [63:0] ex_ps_save_wr_ra, EX_PS_WR_RA;
   wire [31:0] EX_PS_RA_WR_ADDR1, EX_PS_RA_WR_ADDR2;
   
   assign ex_ps_save_wr_ra = {ME2_PS_RA_WR_ADDR1, ME2_PS_RA_WR_ADDR2};
   assign {EX_PS_RA_WR_ADDR1, EX_PS_RA_WR_ADDR2} = EX_PS_WR_RA;
   
   reg64e$ u_reg_ex_ps_save_wr_ra (CLK, ex_ps_save_wr_ra, EX_PS_WR_RA, , CLR, PRE, LD_EX);
   
   wire [31:0] ex_ps_save_mem, EX_PS_SAVE_MEM;
   wire EX_PS_WR_ADDR1_V, EX_PS_WR_ADDR2_V;
   wire [3:0] EX_PS_RA_WR_SIZE1, EX_PS_RA_WR_SIZE2;
   wire EX_PS_PAGE_FAULT_EXC_EXIST, EX_PS_GPROT_EXC_EXIST, EX_PS_EXC_EN_V;
   wire EX_PS_REPNE_WB;
   assign ex_ps_save_mem[31:18] = {ME2_PS_WR_ADDR1_V, ME2_PS_RA_WR_SIZE1, ME2_PS_WR_ADDR2_V, ME2_PS_RA_WR_SIZE2,
                                   ME2_PS_PAGE_FAULT_EXC_EXIST, ME2_PS_GPROT_EXC_EXIST, ME2_PS_EXC_EN_V, ME2_PS_D2_REPNE_WB};
   assign {EX_PS_WR_ADDR1_V, EX_PS_RA_WR_SIZE1, EX_PS_WR_ADDR2_V, EX_PS_RA_WR_SIZE2,
           EX_PS_PAGE_FAULT_EXC_EXIST, EX_PS_GPROT_EXC_EXIST, EX_PS_EXC_EN_V, EX_PS_REPNE_WB} = EX_PS_SAVE_MEM[31:18];

   and2$ and_ex_exc_en_v (EX_EXC_EN_V_OUT, EX_V, EX_PS_EXC_EN_V);
   
   reg32e$ u_reg_ex_ps_save_mem (CLK, ex_ps_save_mem, EX_PS_SAVE_MEM, , CLR, PRE, LD_EX);

   wire nor_ex_exc_exist_out, ex_ps_v_stage_in;
   nor2$ nor_ex_exc_exist (nor_ex_exc_exist_out, EX_PS_PAGE_FAULT_EXC_EXIST, EX_PS_GPROT_EXC_EXIST);
   and2$ and_ex_v_stage_in (ex_ps_v_stage_in, EX_V, nor_ex_exc_exist_out);

   assign EX_V_ME_IN = ex_ps_v_stage_in;
   assign EX_WR_ADDR1_V_ME_IN = EX_PS_WR_ADDR1_V;
   assign EX_WR_ADDR1_ME_IN = EX_PS_RA_WR_ADDR1;
   assign EX_WR_SIZE1_ME_IN = EX_PS_RA_WR_SIZE1;
   assign EX_WR_ADDR2_V_ME_IN = EX_PS_WR_ADDR2_V;
   assign EX_WR_ADDR2_ME_IN = EX_PS_RA_WR_ADDR2;
   assign EX_WR_SIZE2_ME_IN = EX_PS_RA_WR_SIZE2;

   wire EX_V_next; // TODO
   wire [31:0] EX_V_out; 

   wire nor_ex_v_out;
   nor4$ nor_ex_v (nor_ex_v_out, WB_EXC_V_OUT, wb_repne_terminate_all, INTERRUPT_SIGNAL, LSU_OUT_RD_STALL);
   and2$ and_ex_v (EX_V_next, ME2_PS_V, nor_ex_v_out);
   reg32e$ u_EX_v_latch(CLK, {{31{1'b0}}, EX_V_next}, EX_V_out, ,CLR,PRE,LD_EX); 
   assign EX_V = EX_V_out[0]; 
    
    // reg dependency checks
    assign EX_PS_V_OUT_AG_IN = ex_ps_v_stage_in;
   //=============================
   
   // EX_V_next = ME2_PS_V && !MEM_RD_STALL
//    wire EX_V_next = 1'b1; // TODO
//    wire [31:0] EX_V_out; 
//    reg32e$ u_EX_v_latch(CLK, {{31{1'b0}}, EX_V_next}, EX_V_out, ,CLR,PRE,LD_EX); 
//    assign EX_V = EX_V_out[0]; 

    wire [31:0] EX_NEIP_next = ME2_NEIP_OUT;
    wire [31:0] EX_NEIP, EX_NEIP_NOT_TAKEN;
    reg32e$ u_EX_neip_latch(CLK, EX_NEIP_next, EX_NEIP, ,CLR,PRE,LD_EX);
    reg32e$ u_EX_neip_not_taken (CLK, ME2_PS_NEIP_NOT_TAKEN, EX_NEIP_NOT_TAKEN, , CLR, PRE, LD_EX);

    wire [15:0] EX_NCS_next = ME2_NCS_OUT;
    wire [31:0] EX_NCS_out; 
    wire [15:0] EX_NCS;    
    reg32e$ u_EX_ncs_latch(CLK, {{16{1'b0}}, EX_NCS_next}, EX_NCS_out, ,CLR,PRE,LD_EX); 
    assign EX_NCS = EX_NCS_out[15:0]; 

    wire [127:0] EX_CONTROL_STORE_next = ME2_CONTROL_STORE_OUT;
    wire [127:0] EX_CONTROL_STORE;
    reg64e$ u_EX_control_store_latch1(CLK, EX_CONTROL_STORE_next[63:0], EX_CONTROL_STORE[63:0], ,CLR,PRE,LD_EX);
    reg64e$ u_EX_control_store_latch2(CLK, EX_CONTROL_STORE_next[127:64], EX_CONTROL_STORE[127:64], ,CLR,PRE,LD_EX);

    wire [1:0] EX_d2_datasize_all_next = ME2_D2_MEM_SIZE_WB_OUT; 
    wire [31:0] EX_d2_datasize_all_out;
    wire [1:0] EX_d2_datasize_all;
    reg32e$ u_EX_d2_datasize_all_all(CLK, {30'b0,EX_d2_datasize_all_next}, EX_d2_datasize_all_out, ,CLR,PRE,LD_EX);
    assign EX_d2_datasize_all = EX_d2_datasize_all_out[1:0]; 

    wire [2:0] EX_d2_aluk_ex_next = ME2_D2_ALUK_EX_OUT;
    wire [31:0] EX_d2_aluk_ex_out;
    wire [2:0] EX_d2_aluk_ex; 
    reg32e$ u_EX_de_aluk_ex_latch(CLK, {29'b0, EX_d2_aluk_ex_next}, EX_d2_aluk_ex_out, ,CLR,PRE,LD_EX);
    assign EX_d2_aluk_ex = EX_d2_aluk_ex_out[2:0]; 

    wire EX_d2_ld_gpr1_ex_next = ME2_D2_LD_GPR1_WB_OUT;
    wire [31:0] EX_d2_ld_gpr1_ex_out;
    wire EX_d2_ld_gpr1_ex;
    reg32e$ u_EX_de_ld_gpr1_wb_latch (CLK, {31'b0, EX_d2_ld_gpr1_ex_next}, EX_d2_ld_gpr1_ex_out, ,CLR,PRE,LD_EX);
    assign EX_d2_ld_gpr1_ex = EX_d2_ld_gpr1_ex_out[0]; 

    wire EX_d2_dcache_write_ex_next = ME2_D2_MEM_WR_WB_OUT;
    wire [31:0] EX_d2_dcache_write_ex_out;
    wire EX_d2_dcache_write_ex; 
    reg32e$ u_EX_d2_dcache_write_wb_latch(CLK, {31'b0, EX_d2_dcache_write_ex_next}, EX_d2_dcache_write_ex_out, ,CLR,PRE,LD_EX);
    assign EX_d2_dcache_write_ex = EX_d2_dcache_write_ex_out[0]; 

    wire EX_d2_repne_wb_next = ME2_PS_D2_REPNE_WB; //Nelson
    wire [31:0] EX_d2_repne_wb_out; 
    wire EX_d2_repne_wb; 
    reg32e$ u_EX_d2_repne_wb_latch(CLK, {31'b0, EX_d2_repne_wb_next}, EX_d2_repne_wb_out, ,CLR,PRE,LD_EX);
    assign EX_d2_repne_wb = EX_d2_repne_wb_out[0]; 

    wire [31:0] EX_A_next = ME2_A_OUT;
    wire [31:0] EX_B_next = ME2_B_OUT;
    wire [31:0] EX_C_next = ME2_SP_XCHG_DATA_OUT;
    wire [31:0] EX_A, EX_B, EX_C;
    reg32e$ u_EX_a_latch(CLK, EX_A_next, EX_A, ,CLR,PRE,LD_EX);
    reg32e$ u_EX_b_latch(CLK, EX_B_next, EX_B, ,CLR,PRE,LD_EX);
    reg32e$ u_EX_c_latch(CLK, EX_C_next, EX_C, ,CLR,PRE,LD_EX);

    wire [63:0] EX_MM_A_next = ME2_MM_A_OUT;
    wire [63:0] EX_MM_B_next = ME2_MM_B_OUT;
    wire [63:0] EX_MM_A, EX_MM_B;
    reg64e$ u_EX_mm_a_latch(CLK, EX_MM_A_next, EX_MM_A, ,CLR,PRE,LD_EX);
    reg64e$ u_EX_mm_b_latch(CLK, EX_MM_B_next, EX_MM_B, ,CLR,PRE,LD_EX);

    wire [2:0] EX_DR1_next = ME2_DRID1_OUT;
    wire [2:0] EX_DR2_next = ME2_DRID2_OUT;
    wire [31:0] EX_DR1_out, EX_DR2_out;
    wire [2:0] EX_DR1, EX_DR2;
    reg32e$ u_EX_dr1_latch(CLK, {29'b0, EX_DR1_next}, EX_DR1_out, ,CLR,PRE,LD_EX);
    reg32e$ u_EX_dr2_latch(CLK, {29'b0, EX_DR2_next}, EX_DR2_out, ,CLR,PRE,LD_EX);
    assign EX_DR1 = EX_DR1_out[2:0]; 
    assign EX_DR2 = EX_DR2_out[2:0]; 

    wire [31:0] EX_ADDRESS_next = ME2_MEM_WR_ADDR_OUT;
    wire [31:0] EX_ADDRESS;
    reg32e$ u_EX_address_latch(CLK, EX_ADDRESS_next, EX_ADDRESS, ,CLR,PRE,LD_EX);

    //******************************************************************************//
    //*
    //*                                Execute STAGE
    //*
    //*******************************************************************************//

    //Execute Outputs

    wire WB_V; 
    wire WB_V_next;
    wire [31:0] WB_NEIP_next; 
    wire [15:0] WB_NCS_next;
    wire [127:0] WB_CONTROL_STORE_next;

    wire [1:0] WB_de_datasize_all_next;
    wire WB_ex_ld_gpr1_wb_next;
    wire WB_ex_ld_gpr2_wb_next; 
    wire WB_ex_dcache_write_wb_next; 
    wire WB_de_repne_wb_next; 

    wire [31:0] WB_RESULT_A_next;
    wire [31:0] WB_RESULT_B_next;
    wire [31:0] WB_RESULT_C_next;
    wire [31:0] WB_FLAGS_next;
    wire [63:0] WB_RESULT_MM_next; 

    wire [2:0] WB_DR1_next;
    wire [2:0] WB_DR2_next;
    wire [2:0] WB_DR3_next;
    wire [31:0] WB_ADDRESS_next;   

    execute u_execute(
        CLK, PRE, CLR, //not uesd SET/RST

        ex_ps_v_stage_in,
        EX_NEIP,
        EX_NCS,
        EX_CONTROL_STORE,
        //pseudo-control store signals not from control store but generated in decode
        EX_d2_datasize_all,
        EX_d2_aluk_ex, 
        EX_d2_ld_gpr1_ex,
        EX_d2_dcache_write_ex, 
        EX_d2_repne_wb, 

        //execute results
        EX_A, 
        EX_B, 
        EX_C,
        EX_MM_A, 
        EX_MM_B,

        EX_DR1, 
        EX_DR2,
        EX_ADDRESS,

        WB_stall, 
        wb_repne_terminate_all,

        flags_dataforwarded,
        count_dataforwarded,

        WB_V_next,
        WB_NEIP_next, 
        WB_NCS_next,
        WB_CONTROL_STORE_next,

        WB_de_datasize_all_next,
        WB_ex_ld_gpr1_wb_next,
        WB_ex_ld_gpr2_wb_next, 
        WB_ex_dcache_write_wb_next, 
        WB_de_repne_wb_next, 

        WB_RESULT_A_next,
        WB_RESULT_B_next,
        WB_RESULT_C_next,
        WB_FLAGS_next,
        WB_RESULT_MM_next, 

        WB_DR1_next,
        WB_DR2_next,
        WB_ADDRESS_next,   

        DEP_v_ex_ld_gpr1,
        DEP_v_ex_ld_gpr2,
        DEP_v_ex_ld_gpr3,
        Dep_v_ex_ld_seg,
        Dep_v_ex_ld_mm,
        Dep_v_ex_dcache_write,

        WB_ld_latches
    );

   // ADDRESSES FOR WRITING BACK TO MEMORY -- Nelson added
   // TODO: LD_WB = !MEM_WR_STALL
   wire LD_WB;
   //assign LD_WB = 1'b1;
   assign LD_WB = LSU_OUT_WR_STALL_BAR;

   wire [63:0] wb_ps_save_wr_ra, WB_PS_WR_RA;
   wire [31:0] WB_PS_RA_WR_ADDR1, WB_PS_RA_WR_ADDR2;
   
   assign wb_ps_save_wr_ra = {EX_PS_RA_WR_ADDR1, EX_PS_RA_WR_ADDR2};
   assign {WB_PS_RA_WR_ADDR1, WB_PS_RA_WR_ADDR2} = WB_PS_WR_RA;
   
   reg64e$ u_reg_wb_ps_save_wr_ra (CLK, wb_ps_save_wr_ra, WB_PS_WR_RA, , CLR, PRE, LD_WB);
   
   wire [31:0] wb_ps_save_mem, WB_PS_SAVE_MEM;
   wire WB_PS_WR_ADDR1_V, WB_PS_WR_ADDR2_V;
   wire [3:0] WB_PS_RA_WR_SIZE1, WB_PS_RA_WR_SIZE2;
   wire WB_PS_PAGE_FAULT_EXC_EXIST, WB_PS_GPROT_EXC_EXIST, WB_PS_EXC_EN_V;
   assign wb_ps_save_mem[31:19] = {EX_PS_WR_ADDR1_V, EX_PS_RA_WR_SIZE1, EX_PS_WR_ADDR2_V, EX_PS_RA_WR_SIZE2,
                                   EX_PS_PAGE_FAULT_EXC_EXIST, EX_PS_GPROT_EXC_EXIST, EX_PS_EXC_EN_V};
   assign {WB_PS_WR_ADDR1_V, WB_PS_RA_WR_SIZE1, WB_PS_WR_ADDR2_V, WB_PS_RA_WR_SIZE2,
           WB_PS_PAGE_FAULT_EXC_EXIST, WB_PS_GPROT_EXC_EXIST, WB_PS_EXC_EN_V} = WB_PS_SAVE_MEM[31:19];
   
   and2$ and_wb_gen_prot_exc_exist (WB_GEN_PROT_EXC_EXIST_V, WB_V, WB_PS_GPROT_EXC_EXIST);
   and2$ and_wb_page_fault_exc_exist (WB_PAGE_FAULT_EXC_EXIST_V, WB_V, WB_PS_PAGE_FAULT_EXC_EXIST);

   reg32e$ u_reg_wb_ps_save_mem (CLK, wb_ps_save_mem, WB_PS_SAVE_MEM, , CLR, PRE, LD_WB);

   wire nor_wb_exc_exist_out, wb_ps_v_stage_in;
   nor2$ nor_wb_exc_exist (nor_wb_exc_exist_out, WB_PS_PAGE_FAULT_EXC_EXIST, WB_PS_GPROT_EXC_EXIST);
   and2$ and_wb_v_stage_in (wb_ps_v_stage_in, WB_V, nor_wb_exc_exist_out);

   assign WB_V_LSU_IN = wb_ps_v_stage_in;
   assign WB_WR_ADDR1_V_LSU_IN = WB_PS_WR_ADDR1_V;
   assign WB_WR_ADDR1_LSU_IN = WB_PS_RA_WR_ADDR1;
   assign WB_WR_SIZE1_LSU_IN = WB_PS_RA_WR_SIZE1;
   assign WB_WR_ADDR2_V_LSU_IN = WB_PS_WR_ADDR2_V;
   assign WB_WR_ADDR2_LSU_IN = WB_PS_RA_WR_ADDR2;
   assign WB_WR_SIZE2_LSU_IN = WB_PS_RA_WR_SIZE2;

   wire or_wb_exc_out, and_wb_exc_v_out, nor_wb_v_out;
   wire EX_OUT_WB_V_IN;

   // wb_repne_terminate_all = WB_V && termination_conditions && IS_SECOND_UOP && wb_repne
   or2$ or_wb_exc (or_wb_exc_out, WB_PS_PAGE_FAULT_EXC_EXIST, WB_PS_GPROT_EXC_EXIST);
   and2$ and_wb_ints_v (and_wb_exc_v_out, WB_V, or_wb_exc_out);
   nor3$ nor_wb_v (nor_wb_v_out, and_wb_exc_v_out, wb_repne_terminate_all, INTERRUPT_SIGNAL);
   and2$ and_wb_v (EX_OUT_WB_V_IN, EX_V, nor_wb_v_out);
   assign WB_EXC_V_OUT = and_wb_exc_v_out;
   assign WB_FLUSH_PIPELINE_BAR = nor_wb_v_out;

   wire [31:0] WB_V_out;
   reg32e$ u_WB_v_latch(CLK, {{31{1'b0}}, EX_OUT_WB_V_IN}, WB_V_out, , CLR, PRE, LD_WB); 
   assign WB_V = WB_V_out[0]; 
   //========================================================
   
   // WB_V_next = EX_V
    //register between EX and WB
//    wire [31:0] WB_V_out;
//    reg32e$ u_WB_v_latch(CLK, {{31{1'b0}}, WB_V_next}, WB_V_out, ,CLR,PRE,LD_WB); 
//    assign WB_V = WB_V_out[0]; 

    wire [31:0] WB_NEIP, WB_NEIP_NOT_TAKEN;
    reg32e$ u_WB_neip_latch(CLK, WB_NEIP_next, WB_NEIP, ,CLR,PRE,LD_WB);
    reg32e$ u_WB_neip_not_taken (CLK, EX_NEIP_NOT_TAKEN, WB_NEIP_NOT_TAKEN, ,CLR,PRE,LD_WB);

    wire [31:0] WB_NCS_out;
    wire [15:0] WB_NCS;
    reg32e$ u_WB_ncs_latch(CLK, {16'b0, WB_NCS_next}, WB_NCS_out, ,CLR,PRE,LD_WB);
    assign WB_NCS = WB_NCS_out[15:0];

    wire [127:0] WB_CONTROL_STORE;
    reg64e$ u_WB_control_store_latch1 (CLK, WB_CONTROL_STORE_next[127:64], WB_CONTROL_STORE[127:64], ,CLR,PRE,LD_WB);
    reg64e$ u_WB_control_store_latch2 (CLK, WB_CONTROL_STORE_next[63:0], WB_CONTROL_STORE[63:0], ,CLR,PRE,LD_WB);

    wire [31:0] WB_de_datasize_all_out; 
    wire [1:0] WB_de_datasize_all; 
    reg32e$ u_WB_de_datasize_all_latch(CLK, {30'b0, WB_de_datasize_all_next}, WB_de_datasize_all_out, ,CLR,PRE,LD_WB);
    assign WB_de_datasize_all = WB_de_datasize_all_out[1:0]; 

    wire [31:0] WB_ex_ld_gpr1_wb_out; 
    wire WB_ex_ld_gpr1_wb; 
    reg32e$ u_WB_ex_ld_gpr1_wb_latch(CLK, {31'b0, WB_ex_ld_gpr1_wb_next}, WB_ex_ld_gpr1_wb_out, ,CLR,PRE,LD_WB);
    assign WB_ex_ld_gpr1_wb = WB_ex_ld_gpr1_wb_out[0]; 

    wire [31:0] WB_ex_ld_gpr2_wb_out; 
    wire WB_ex_ld_gpr2_wb; 
    reg32e$ u_WB_ex_ld_gpr2_wb_latch(CLK, {31'b0, WB_ex_ld_gpr2_wb_next}, WB_ex_ld_gpr2_wb_out, ,CLR,PRE,LD_WB);
    assign WB_ex_ld_gpr2_wb = WB_ex_ld_gpr2_wb_out[0]; 

    wire [31:0] WB_ex_dcache_write_wb_out; 
    wire WB_ex_dcache_write_wb; 
    reg32e$ u_WB_ex_dcache_write_wb_latch(CLK, {31'b0, WB_ex_dcache_write_wb_next}, WB_ex_dcache_write_wb_out, ,CLR,PRE,LD_WB);
    assign WB_ex_dcache_write_wb = WB_ex_dcache_write_wb_out[0]; 

    wire [31:0] WB_de_repne_wb_out; 
    wire WB_de_repne_wb; 
    reg32e$ u_WB_de_repne_wb_latch(CLK, {31'b0, WB_de_repne_wb_next}, WB_de_repne_wb_out, ,CLR,PRE,LD_WB);
    assign WB_de_repne_wb = WB_de_repne_wb_out[0]; 

    wire [31:0] WB_RESULT_A;
    reg32e$ u_WB_RESULT_A_latch(CLK, WB_RESULT_A_next, WB_RESULT_A, ,CLR,PRE,LD_WB);

    wire [31:0] WB_RESULT_B;
    reg32e$ u_WB_RESULT_B_latch(CLK, WB_RESULT_B_next, WB_RESULT_B, ,CLR,PRE,LD_WB);

    wire [31:0] WB_RESULT_C;
    reg32e$ u_WB_RESULT_C_latch(CLK, WB_RESULT_C_next, WB_RESULT_C, ,CLR,PRE,LD_WB);

    wire [31:0] WB_FLAGS;
    reg32e$ u_WB_FLAGS_latch(CLK, WB_FLAGS_next, WB_FLAGS, ,CLR,PRE,LD_WB);

    wire [63:0] WB_RESULT_MM; 
    reg64e$ u_WB_RESULT_MM_latch(CLK, WB_RESULT_MM_next, WB_RESULT_MM, ,CLR,PRE,LD_WB);

    wire [31:0] WB_DR1_out; 
    wire [31:0] WB_DR2_out;
    wire [2:0] WB_DR1, WB_DR2;
    reg32e$ u_WB_DR1_latch(CLK, {29'b0, WB_DR1_next}, WB_DR1_out, ,CLR,PRE,LD_WB);
    reg32e$ u_WB_DR2_latch(CLK, {29'b0, WB_DR2_next}, WB_DR2_out, ,CLR,PRE,LD_WB);
    assign WB_DR1 = WB_DR1_next[2:0];
    assign WB_DR2 = WB_DR2_next[2:0];

    wire [31:0] WB_ADDRESS; 
    reg32e$ u_WB_ADDRESS_latch(CLK, WB_ADDRESS_next, WB_ADDRESS, ,CLR,PRE,LD_WB);

    //******************************************************************************//
    //*
    //*                                Writeback STAGE
    //*
    //*******************************************************************************//

    writeback u_writeback(
        CLK, PRE, CLR, //not uesd SET/RST

        wb_ps_v_stage_in,
        WB_NEIP_NOT_TAKEN,
        WB_NEIP,
        WB_NCS,
        WB_CONTROL_STORE,
       //pseudo-control store signals not from control store but generated in decode
        WB_de_datasize_all,
        WB_ex_ld_gpr1_wb,
        WB_ex_ld_gpr2_wb,
        WB_ex_dcache_write_wb,
        WB_de_repne_wb, 

        WB_RESULT_A, 
        WB_RESULT_B, 
        WB_RESULT_C,
        WB_FLAGS,
        WB_RESULT_MM,

        WB_DR1,
        WB_DR2,
        WB_ADDRESS,

        In_write_ready, 

        WB_Final_DR1,
        WB_Final_DR2,
        WB_Final_DR3,
        WB_Final_data1,
        WB_Final_data2,
        WB_Final_data3,
        WB_Final_ld_gpr1,
        WB_Final_ld_gpr2,
        WB_Final_ld_gpr3,
        WB_Final_datasize,
        WB_Final_DR3_datasize,
        WB_Final_ld_seg, 
        WB_Final_MM_Data,
        WB_Final_ld_mm, 
        WB_Final_EIP, 
        WB_Final_ld_eip, 
        WB_Final_CS, 
        WB_Final_ld_cs, 
        WB_Final_Flags,
        WB_Final_ld_flags,
        WB_Final_Dcache_Data,
        WB_Final_Dcache_address,
        WB_Final_Dcache_Write,

        DEP_v_wb_ld_gpr1,
        DEP_v_wb_ld_gpr2,
        DEP_v_wb_ld_gpr3,
        DEP_v_wb_ld_seg,
        DEP_v_wb_ld_mm,
        DEP_v_wb_dcache_write,

        wb_halt_all, 
        wb_repne_terminate_all,
        WB_stall,

        flags_dataforwarded,
        count_dataforwarded
    );

endmodule
