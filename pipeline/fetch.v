// 16 bytes from icache in one access
module fetch (
   input CLK, reset, set,

   input [31:0] EIP,
   input [15:0] CS,

   // inputs from ICACHE
   input [127:0] ICACHE_RD_DATA,
   input ICACHE_READY,

   input [31:0] jmp_fp, trap_fp,
   input [1:0] fp_mux,
   input load_eip,

   input REG_DEP_STALL, MEM_DEP_STALL,
   input JMP_STALL, EXC_STALL,

   output [31:0] EIP_OUT,
   output [15:0] CS_OUT,

   // outputs to ICACHE
   output [31:0] ICACHE_ADDR_OUT,
   output [4:0] ICACHE_SIZE_OUT,
   output ICACHE_EN_OUT,

   output segment_limit_exception,
   output [127:0] IR_OUT,

   output [3:0] instr_length_updt,
   output [15:0] opcode,
   output [1:0] prefix_size,
   output prefix_present, segment_override, operand_override, repeat_prefix,
   output modrm_present, imm_present,
   output [1:0] imm_size,
   output sib_present, disp_present, disp_size,
   output [3:0] imm_sel,
   output [2:0] disp_sel,
   output offset_present,
   output opcode_size,
   output [1:0] offset_size,
   output [2:0] segID,
   output [7:0] modrm, sib,
   output [2:0] modrm_sel,
   output [7:0] control_store_address
);

   //The four buffers for the fetch unit
   wire [127:0] FE_buf_0_in, FE_buf_1_in, FE_buf_2_in, FE_buf_3_in;	//the buffer register inputs
   wire [127:0] FE_buf_0_out, FE_buf_1_out, FE_buf_2_out, FE_buf_3_out;
   wire 	FE_buf_0_en, FE_buf_1_en, FE_buf_2_en, FE_buf_3_en;
   wire [127:0] CURRENT_IR;

   assign IR_OUT = CURRENT_IR;
   assign CS_OUT = CS;

   // assign FE_buf_0_en = 1;
   // assign FE_buf_1_en = 1;
   // assign FE_buf_2_en = 1;
   // assign FE_buf_3_en = 1;
   // assign FE_buf_3_in = 128'h0F6FEB254B212F9681773D090CDB1283;
   // assign FE_buf_2_in = 128'h7E6D39201F21D32285BC148878235B49;
   // assign FE_buf_1_in = 128'h0F6FEB254B212F9681773D090CDB1283;
   // assign FE_buf_0_in = 128'h7E6D39201F21D32285BC148878235B49;

   // FE_buf_0_en = (buf_ptr == 2'b00) && (ICACHE_RD_STALL = 1'b0)

//   wire buf_ptr_rst;
//   wire [7:0] buf_ptr_data_in;
//   wire buf_ptr_en;
//   wire buf_ptr_set;
//   wire buf_ptr_ld_data;
//   wire buf_ptr_up;
//   wire buf_ptr_cout;
//   wire [7:0] buf_ptr_Qout;
//   wire [1:0] buf_ptr;

//   assign buf_ptr_data_in = 8'b0;
//   assign buf_ptr_set = 1'b1;
//   assign buf_ptr_ld_data = 1'b0;
//   assign buf_ptr_up = 1'b1;
//   assign buf_ptr = buf_ptr_Qout[1:0];
// module syn_cntr8$(CLK,CLR,D,EN,PRE,PL,UP,COUT,Q);
//   syn_cntr8$ buf_ptr_cntr (CLK, buf_ptr_rst, buf_ptr_data_in, buf_ptr_en, buf_ptr_set, buf_ptr_ld_data, buf_ptr_up, buf_ptr_cout, buf_ptr_Qout);



/*
fetch_v = !(full or flush or page_fault_exception)

read_ptr_en = !dep_stall && !empty
buf_ptr_en = !full && !icache_rd_stall
full = (next_buf_ptr == next_read_ptr)
empty = (next_buf_ptr < (read_ptr + 0x10))

//empty = (next_buf_ptr == read_ptr)

next_buf_ptr = if (icache_rd_stall) ? Buf_ptr : (buf_ptr + 1)
next_read_ptr = if (dep_stall) ? Read_ptr : (read_ptr + length)

*/

   wire rst_state, flush_state, exc_state, fill_state, empty_state, full_state;
   wire rst_state_bar, flush_state_bar, exc_state_bar, fill_state_bar, empty_state_bar, full_state_bar;
   wire Dflush_state, Dexc_state, Dfill_state, Dempty_state, Dfull_state;

   wire [1:0] buf_ptr, buf_ptr_bar;
   wire [3:0] prev_instr_len;

   wire [31:0] fetch_ptr, temp_eip;
   wire [5:0] read_ptr, read_ptr_bar;

   wire flush, dep_stall, flush_bar, dep_stall_bar;
   wire buf_full, buf_empty;
   wire buf_full_bar, buf_empty_bar;

   wire [1:0] next_buf_ptr, next_buf_ptr_bar, inc_buf_ptr;
   wire [5:0] next_read_ptr;

   wire buf_ptr_en, read_ptr_en;

   wire nor_v_fetch_out, nor_read_ptr_en_out, nor_buf_ptr_en_out,
        xor_inc_buf_ptr_out;
   wire [1:0] mux_next_buf_ptr_out, xnor_full_out, xnor_empty_out;
   wire and_full_out, and_empty_out, nand_full_out;

   or2$ or_flush (flush, JMP_STALL, EXC_STALL);
   nor2$ nor_flush (flush_bar, JMP_STALL, EXC_STALL);
   or2$ or_dep_stall (dep_stall, REG_DEP_STALL, MEM_DEP_STALL);
   nor2$ nor_dep_stall (dep_stall_bar, REG_DEP_STALL, MEM_DEP_STALL);

   nor3$ nor_v_fetch (nor_v_fetch_out, full_state, flush, exc_state);
   assign IFU_V_FETCH_IN = nor_v_fetch_out;

   wire or_read_ptr_en_out, and_read_ptr_en_out;

   nor2$ nor_read_ptr_en (nor_read_ptr_en_out, dep_stall, buf_empty);
   or2$ or_read_ptr_en (or_read_ptr_en_out, fill_state, full_state);
   and2$ and_read_ptr_en (and_read_ptr_en_out, nor_read_ptr_en_out, or_read_ptr_en_out);
   assign read_ptr_en = and_read_ptr_en_out;

   wire and_buf_ptr_en_out;
   nor2$ nor_buf_ptr_en (nor_buf_ptr_en_out, buf_full, IFU_ICACHE_RD_STALL_OUT); 
   and2$ and_buf_ptr_en (and_buf_ptr_en_out, nor_buf_ptr_en_out, Dfill_state);
   assign buf_ptr_en = and_buf_ptr_en_out;

   xor2$ xor_inc_buf_ptr1 (xor_inc_buf_ptr_out, buf_ptr[1], buf_ptr[0]);
   assign inc_buf_ptr[1] = xor_inc_buf_ptr_out;
   assign inc_buf_ptr[0] = buf_ptr_bar[0];

   mux2_2 mux_next_buf_ptr (mux_next_buf_ptr_out, inc_buf_ptr, buf_ptr, IFU_ICACHE_RD_STALL_OUT);
   assign next_buf_ptr = mux_next_buf_ptr_out;
   inv1$ inv_next_buf_ptr [1:0] (next_buf_ptr_bar, next_buf_ptr);

   xnor2$ xnor_full [1:0] (xnor_full_out, next_buf_ptr, next_read_ptr[5:4]);
   and2$ and_full (and_full_out, xnor_full_out[1], xnor_full_out[0]);
   nand2$ nand_full (nand_full_out, xnor_full_out[1], xnor_full_out[0]);
   assign buf_full = and_full_out;
   assign buf_full_bar = nand_full_out;

   wire and9_out, and10_out, and11_out, and12_out, or3_out,
        and13_out, and14_out, and15_out, and16_out, or4_out, nor4_out;

   // empty if 16B not available to read
   and4$
      and9 (and9_out, read_ptr_bar[5], read_ptr_bar[4], next_buf_ptr_bar[1], next_buf_ptr[0]),
      and10 (and10_out, read_ptr_bar[5], read_ptr[4], next_buf_ptr[1], next_buf_ptr_bar[0]),
      and11 (and11_out, read_ptr[5], read_ptr_bar[4], next_buf_ptr[1], next_buf_ptr[0]),
      and12 (and12_out, read_ptr[5], read_ptr[4], next_buf_ptr_bar[1], next_buf_ptr_bar[0]);
   or4$ or3 (or3_out, read_ptr[3], read_ptr[2], read_ptr[1], read_ptr[0]);
   and2$
      and13 (and13_out, and9_out, or3_out),
      and14 (and14_out, and10_out, or3_out),
      and15 (and15_out, and11_out, or3_out),
      and16 (and16_out, and12_out, or3_out);
   or4$ or4 (or4_out, and13_out, and14_out, and15_out, and16_out);
   nor4$ nor4 (nor4_out, and13_out, and14_out, and15_out, and16_out);
   assign buf_empty = or4_out;
   assign buf_empty_bar = nor4_out;

   // fetch_pointer update
   //
   // buf_ptr_rst = ! ((RST == 1'b0) | flush)
   // buf_ptr_en = !buf_full && (no exception)
   //
   // read_ptr_rst = ! ((RST == 1'b0) | flush)
   // read_ptr_en = ! (stall | exception)

   wire [31:0] Qread_ptr, QBARread_ptr;
   wire [31:0] Dread_ptr;

   wire read_ptr_rst;
   wire read_ptr_set;

   wire reset_bar, nor_reset_out;

   wire [31:0] add_read_ptr_out;
   wire [15:0] mux_next_read_ptr_out;
   adder32_w_carry_in add_read_ptr (add_read_ptr_out, , {26'h0, read_ptr}, {28'b0, instr_length_updt}, 1'b0);
   mux2_16$ mux_next_read_ptr (mux_next_read_ptr_out, {10'b0, add_read_ptr_out[5:0]}, {10'b0, read_ptr}, dep_stall);
   assign next_read_ptr = mux_next_read_ptr_out[5:0];

   assign Dread_ptr[31:6] = 26'b0;
   assign Dread_ptr[5:0] = mux_next_read_ptr_out[5:0];
   // asynchronous reset okay ok flush?
   inv1$ inv0 (reset_bar, reset);
   nor2$ nor_reset (nor_reset_out, reset_bar, flush);

   assign read_ptr_rst = nor_reset_out;
   assign read_ptr_set = set;
   reg32e$ reg_read_ptr (CLK, Dread_ptr, Qread_ptr, QBARread_ptr, read_ptr_rst, read_ptr_set, read_ptr_en);
   assign read_ptr = Qread_ptr[5:0];
   assign read_ptr_bar = QBARread_ptr[5:0];

   wire [31:0] Dfetch_ptr, Qfetch_ptr, QBARfetch_ptr,
               Dbuf_ptr, Qbuf_ptr, QBARbuf_ptr,
               Dtemp_eip, Qtemp_eip, QBARtemp_eip,
//               Dtemp_cs, Qtemp_cs, QBARtemp_cs,
               Dtemp_instr_len, Qtemp_instr_len, QBARtemp_instr_len;

   wire fetch_ptr_rst, fetch_ptr_set, fetch_ptr_en,
        buf_ptr_rst, buf_ptr_set,
        temp_eip_rst, temp_eip_set, temp_eip_en,
//        temp_cs_rst, temp_cs_set, temp_cs_en,
        temp_instr_len_rst, temp_instr_len_set, temp_instr_len_en;

   wire [31:0] Dfetch_state, Qfetch_state, QBARfetch_state;
   wire fetch_state_rst, fetch_state_set, fetch_state_en;

   wire [31:0] add_fetch_ptr_out, add_eip_cs_out, add_eip_cs_2_out,
               mux_fetch_ptr_out, mux_ifu_addr_out;
   wire [31:0] add_eip_len_out, mux_temp_eip_out;

   wire [31:0] IFU_FETCH_POINTER_IN;

   wire or_rst_flush_out;
   or2$ or_rst_flush (or_rst_flush_out, rst_state, flush_state);

   adder32_w_carry_in add_fetch_ptr (add_fetch_ptr_out, , fetch_ptr, 32'h10, 1'b0);
   adder32_w_carry_in add_eip_cs (add_eip_cs_out, , EIP, {CS, 16'b0}, 1'b0);
   //adder32_w_carry_in add_eip_cs_2 (add_eip_cs_2_out, , add_eip_cs_out, 32'h10, 1'b0);
   //mux2_32 mux_fetch_ptr (mux_fetch_ptr_out, add_fetch_ptr_out, add_eip_cs_2_out, or_rst_flush_out);
   mux2_32 mux_fetch_ptr (mux_fetch_ptr_out, add_fetch_ptr_out, add_eip_cs_out, or_rst_flush_out);
   assign Dfetch_ptr = mux_fetch_ptr_out;
   assign fetch_ptr = Qfetch_ptr;

   mux2_32 mux_ifu_addr (mux_ifu_addr_out, fetch_ptr, add_eip_cs_out, or_rst_flush_out);
   assign IFU_FETCH_POINTER_IN = mux_ifu_addr_out;

   assign fetch_ptr_rst = buf_ptr_rst;
   assign fetch_ptr_set = set;
   or2$ or_fetch_ptr_en (fetch_ptr_en, buf_ptr_en, or_rst_flush_out);
   reg32e$ reg_fetch_ptr (CLK, Dfetch_ptr, Qfetch_ptr, QBARfetch_ptr, fetch_ptr_rst, fetch_ptr_set, fetch_ptr_en);

   assign Dbuf_ptr[31:2] = 30'b0;
   assign Dbuf_ptr[1:0] = next_buf_ptr;
   assign buf_ptr_rst = nor_reset_out;
   assign buf_ptr_set = set;
   reg32e$ reg_buf_ptr (CLK, Dbuf_ptr, Qbuf_ptr, QBARbuf_ptr, buf_ptr_rst, buf_ptr_set, buf_ptr_en);
   assign buf_ptr = Qbuf_ptr[1:0];
   assign buf_ptr_bar = QBARbuf_ptr[1:0];

   adder32_w_carry_in add_eip_len (add_eip_len_out, , temp_eip, {28'b0, prev_instr_len}, 1'b0);
   mux2_32 mux_temp_eip (mux_temp_eip_out, add_eip_len_out, EIP, or_rst_flush_out);
   assign Dtemp_eip = mux_temp_eip_out;

   assign EIP_OUT = mux_temp_eip_out;

   assign temp_eip_rst = buf_ptr_rst;
   assign temp_eip_set = set;
   or2$ or_temp_eip_en (temp_eip_en, read_ptr_en, or_rst_flush_out);
   reg32e$ reg_temp_eip (CLK, Dtemp_eip, Qtemp_eip, QBARtemp_eip, temp_eip_rst, temp_eip_set, temp_eip_en);
   assign temp_eip = Qtemp_eip;

   // mux2_16$ mux_temp_cs (mux_temp_cs_out, temp_cs, CS, rst_state);
   // reg32e$ reg_temp_cs (CLK, Dtemp_cs, Qtemp_cs, QBARtemp_cs, temp_cs_rst, temp_cs_set, temp_cs_en);
   assign Dtemp_instr_len[31:4] = 28'b0;
   assign Dtemp_instr_len[3:0] = instr_length_updt;
   assign prev_instr_len = Qtemp_instr_len[3:0];
   assign temp_instr_len_rst = buf_ptr_rst;
   assign temp_instr_len_set = set;
   assign temp_instr_len_en = read_ptr_en;
   reg32e$ reg_temp_instr_len (CLK, Dtemp_instr_len, Qtemp_instr_len, QBARtemp_instr_len, temp_instr_len_rst, temp_instr_len_set, temp_instr_len_en);

   assign Dfetch_state[31:5] = 27'b0;
   assign fetch_state_rst = reset;
   assign fetch_state_set = 1'b1;
   assign fetch_state_en = 1'b1;
   reg32e$ reg_fetch_state (CLK, Dfetch_state, Qfetch_state, QBARfetch_state, fetch_state_rst, fetch_state_set, fetch_state_en);
   assign {flush_state, exc_state, fill_state, empty_state, full_state} = Qfetch_state[4:0];
   assign {flush_state_bar, exc_state_bar, fill_state_bar, empty_state_bar, full_state_bar} = QBARfetch_state[4:0];

   wire or_rst_state0_out, or_rst_state1_out;
   or3$ or_rst_state0 (or_rst_state0_out, flush_state, exc_state, fill_state);
   or2$ or_rst_state1 (or_rst_state1_out, empty_state, full_state);
   nor2$ or_rst_state2 (rst_state, or_rst_state0_out, or_rst_state1_out);

   wire ifu_icache_rd_stall_out_bar, ifu_page_fault_exc_out_bar;
   wire and0_out, and1_out, or0_out,
        and2_out, and3_out, and4_out, or1_out;

   assign Dflush_state = flush;

   inv1$
      inv1 (ifu_icache_rd_stall_out_bar, IFU_ICACHE_RD_STALL_OUT),
      inv2 (ifu_page_fault_exc_out_bar, IFU_PAGE_FAULT_EXC_OUT);

   wire and_exc0_out, and_exc1_out, and_exc2_out, or_exc0_out;

   and3$
      and_exc0 (and_exc0_out, flush_state_bar, exc_state, fill_state_bar),
      and_exc1 (and_exc1_out, empty_state_bar, full_state_bar, flush_bar);
   and2$ and_exc2 (and_exc2_out, and_exc0_out, and_exc1_out);
   or2$ or_exc0 (or_exc0_out, and_exc2_out, IFU_PAGE_FAULT_EXC_OUT);
   assign Dexc_state = or_exc0_out;

   wire and_fill0_out, and_fill1_out, and_fill2_out, and_fill3_out,
        and_fill4_out, and_fill5_out, and_fill6_out, and_fill7_out,
        and_fill8_out, and_fill9_out, and_fill10_out, and_fill11_out,
        and_fill12_out, and_fill13_out, and_fill14_out, and_fill15_out,
        and_fill16_out, and_fill17_out, or_fill0_out, or_fill1_out, or_fill2_out;

   and3$
      and_fill0 (and_fill0_out, flush_state_bar, exc_state_bar, fill_state_bar),
      and_fill1 (and_fill1_out, empty_state, full_state_bar, ifu_icache_rd_stall_out_bar), 
      and_fill2 (and_fill2_out, ifu_page_fault_exc_out_bar, buf_empty_bar, flush_bar),
      and_fill3 (and_fill3_out, and_fill0_out, and_fill1_out, and_fill2_out),

      and_fill4 (and_fill4_out, flush_state_bar, exc_state_bar, fill_state),
      and_fill5 (and_fill5_out, empty_state_bar, full_state_bar, IFU_ICACHE_RD_STALL_OUT),
      and_fill6 (and_fill6_out, ifu_page_fault_exc_out_bar, buf_empty_bar, flush_bar),
      and_fill7 (and_fill7_out, and_fill4_out, and_fill5_out, and_fill6_out),

      and_fill8 (and_fill8_out, empty_state_bar, full_state_bar, ifu_icache_rd_stall_out_bar),
      and_fill9 (and_fill9_out, ifu_page_fault_exc_out_bar, buf_full_bar, flush_bar),
      and_fill10 (and_fill10_out, and_fill4_out, and_fill8_out, and_fill9_out),

      and_fill11 (and_fill11_out, flush_state, exc_state_bar, fill_state_bar),
      and_fill12 (and_fill12_out, empty_state_bar, full_state_bar, ifu_icache_rd_stall_out_bar);
   and2$ and_fill13 (and_fill13_out, ifu_page_fault_exc_out_bar, flush_bar);
   and3$
      and_fill14 (and_fill14_out, and_fill11_out, and_fill12_out, and_fill13_out),

      and_fill15 (and_fill15_out, flush_state_bar, exc_state_bar, fill_state_bar),
      and_fill16 (and_fill16_out, empty_state_bar, full_state, buf_full_bar),
      and_fill17 (and_fill17_out, and_fill15_out, and_fill16_out, flush_bar);

   or3$ or_fill0 (or_fill0_out, and_fill3_out, and_fill7_out, and_fill10_out);
   or2$
      or_fill1 (or_fill1_out, and_fill14_out, and_fill17_out),
      or_fill2 (or_fill2_out, or_fill0_out, or_fill1_out);
   assign Dfill_state = or_fill2_out;

   wire and_empty0_out, and_empty1_out, and_empty2_out, and_empty3_out,
        and_empty4_out, and_empty5_out, and_empty6_out, and_empty7_out,
        and_empty8_out, and_empty9_out, and_empty10_out, and_empty11_out,
        and_empty12_out, and_empty13_out, and_empty14_out, and_empty15_out,
        or_empty0_out, or_empty1_out, or_empty2_out;
   and3$
      and_empty0 (and_empty0_out, flush_state_bar, exc_state_bar, fill_state_bar),
      and_empty1 (and_empty1_out, full_state_bar, ifu_page_fault_exc_out_bar, buf_empty),
      and_empty2 (and_empty2_out, and_empty0_out, and_empty1_out, flush_bar),

      and_empty3 (and_empty3_out, flush_state_bar, exc_state_bar, empty_state_bar),
      and_empty4 (and_empty4_out, full_state_bar, IFU_ICACHE_RD_STALL_OUT, ifu_page_fault_exc_out_bar);
   and2$ and_empty5 (and_empty5_out, buf_empty, flush_bar);
   and3$
      and_empty6 (and_empty6_out, and_empty3_out, and_empty4_out, and_empty5_out),

      and_empty7 (and_empty7_out, exc_state_bar, fill_state_bar, empty_state_bar),
      and_empty8 (and_empty8_out, full_state_bar, IFU_ICACHE_RD_STALL_OUT, ifu_page_fault_exc_out_bar),
      and_empty9 (and_empty9_out, and_empty7_out, and_empty8_out, flush_bar),

      and_empty10 (and_empty10_out, flush_state_bar, exc_state_bar, fill_state_bar),
      and_empty11 (and_empty11_out, full_state_bar, IFU_ICACHE_RD_STALL_OUT, ifu_page_fault_exc_out_bar),
      and_empty12 (and_empty12_out, and_empty10_out, and_empty11_out, flush_bar),

      and_empty13 (and_empty13_out, flush_state_bar, exc_state_bar, fill_state_bar),
      and_empty14 (and_empty14_out, empty_state_bar, full_state_bar, ifu_page_fault_exc_out_bar);
   and2$ and_empty15 (and_empty15_out, and_empty13_out, and_empty14_out);
   or3$ or_empty0 (or_empty0_out, and_empty2_out, and_empty6_out, and_empty9_out);
   or2$
      or_empty1 (or_empty1_out, and_empty12_out, and_empty15_out),
      or_empty2 (or_empty2_out, or_empty0_out, or_empty1_out);
   assign Dempty_state = or_empty2_out;

   wire and_full0_out, and_full1_out, and_full2_out, and_full3_out,
        and_full4_out, and_full5_out, and_full6_out, or_full0_out;
   and3$
      and_full0 (and_full0_out, flush_state_bar, exc_state_bar, fill_state),
      and_full1 (and_full1_out, empty_state_bar, full_state_bar, ifu_icache_rd_stall_out_bar),
      and_full2 (and_full2_out, ifu_page_fault_exc_out_bar, buf_full, flush_bar),
      and_full3 (and_full3_out, and_full0_out, and_full1_out, and_full2_out),

      and_full4 (and_full4_out, flush_state_bar, exc_state_bar, fill_state_bar),
      and_full5 (and_full5_out, empty_state_bar, full_state, buf_full),
      and_full6 (and_full6_out, and_full4_out, and_full5_out, flush_bar);
   or2$ or_full0 (or_full0_out, and_full3_out, and_full6_out);
   assign Dfull_state = or_full0_out;

   assign Dfetch_state[4:0] = {Dflush_state, Dexc_state, Dfill_state, Dempty_state, Dfull_state};

   reg128e u_FE_buf_0 (CLK, FE_buf_0_in, FE_buf_0_out, , reset, set, FE_buf_0_en);
   reg128e u_FE_buf_1 (CLK, FE_buf_1_in, FE_buf_1_out, , reset, set, FE_buf_1_en);
   reg128e u_FE_buf_2 (CLK, FE_buf_2_in, FE_buf_2_out, , reset, set, FE_buf_2_en);
   reg128e u_FE_buf_3 (CLK, FE_buf_3_in, FE_buf_3_out, , reset, set, FE_buf_3_en);

   wire or_state0_out, and_state0_out, and_state1_out, or_state1_out;

   or3$ or_state0 (or_state0_out, flush_state, empty_state, fill_state);
   and2$ and_state0 (and_state0_out, Dfill_state, or_state0_out);
   and2$ and_state1 (and_state1_out, fill_state, Dfull_state);
   or2$ or_state1 (or_state1_out, and_state0_out, and_state1_out);

   and4$
      and5 (FE_buf_0_en, buf_ptr_bar[1], buf_ptr_bar[0], ifu_icache_rd_stall_out_bar, or_state1_out),
      and6 (FE_buf_1_en, buf_ptr_bar[1], buf_ptr[0], ifu_icache_rd_stall_out_bar, or_state1_out),
      and7 (FE_buf_2_en, buf_ptr[1], buf_ptr_bar[0], ifu_icache_rd_stall_out_bar, or_state1_out),
      and8 (FE_buf_3_en, buf_ptr[1], buf_ptr[0], ifu_icache_rd_stall_out_bar, or_state1_out);

   //temporary read_ptr assign until the fetch is finished
   //Values of the fetch buffers until the fetch unit is finished
   wire [127:0] mux_buf_0_out, mux_buf_1_out, mux_buf_2_out, mux_buf_3_out;
   wire [127:0] IFU_IR_DATA_OUT;
   wire ICACHE_RW_OUT;

//   mux2_128
//      mux_buf_0 (mux_buf_0_out, FE_buf_0_out, IFU_IR_DATA_OUT, buf_empty),
//      mux_buf_1 (mux_buf_1_out, FE_buf_1_out, IFU_IR_DATA_OUT, buf_empty),
//      mux_buf_2 (mux_buf_2_out, FE_buf_2_out, IFU_IR_DATA_OUT, buf_empty),
//      mux_buf_3 (mux_buf_3_out, FE_buf_3_out, IFU_IR_DATA_OUT, buf_empty);
//   FE_full_shifter FE_full_shifter1 (mux_buf_0_out, mux_buf_1_out, mux_buf_2_out, mux_buf_3_out, read_ptr, CURRENT_IR);

   FE_full_shifter FE_full_shifter1 (FE_buf_0_out, FE_buf_1_out, FE_buf_2_out, FE_buf_3_out, read_ptr, CURRENT_IR);

   ifu u_ifu (CLK, reset, set, IFU_V_FETCH_IN, IFU_FETCH_POINTER_IN, 16'b0, ICACHE_RD_DATA, ICACHE_READY, ICACHE_ADDR_OUT, ICACHE_SIZE_OUT, ICACHE_RW_OUT, ICACHE_EN_OUT, IFU_ICACHE_RD_STALL_OUT, IFU_IR_DATA_OUT, IFU_PAGE_FAULT_EXC_OUT);

   assign FE_buf_0_in = IFU_IR_DATA_OUT;
   assign FE_buf_1_in = IFU_IR_DATA_OUT;
   assign FE_buf_2_in = IFU_IR_DATA_OUT;
   assign FE_buf_3_in = IFU_IR_DATA_OUT;

   decode_stage1 u_decode_stage1 (CLK, set, reset,
				  CURRENT_IR, ,
				  instr_length_updt,
				  opcode,
				  prefix_size,
				  prefix_present, segment_override, operand_override, repeat_prefix,
				  modrm_present, imm_present,
				  imm_size,
				  sib_present, disp_present, disp_size,
				  imm_sel,
				  disp_sel,
				  offset_present,
				  opcode_size,
				  offset_size,
				  segID,
				  modrm, sib,
				  modrm_sel,
                  control_store_address
    );

endmodule

module FE_full_shifter(
   input [127:0] A, B, C, D,
   input [5:0] address,
   output [127:0] OutputA
);

   assign dir = 0;
   wire [127:0] AB_out, BC_out, CD_out, DA_out;
   
   shift128$ AB(A, B, dir, address[3:0], AB_out);
   shift128$ BC(B, C, dir, address[3:0], BC_out);
   shift128$ CD(C, D, dir, address[3:0], CD_out);
   shift128$ DA(D, A, dir, address[3:0], DA_out);
   
   mux4_128 selector(OutputA, AB_out, BC_out, CD_out, DA_out, address[4], address[5]);
	
endmodule

module shift128$ (
    input [127:0] Din_high,
    input [127:0] Din_low,
    input dir,
    input [3:0] amnt,
    output [127:0] Dout
);

   wire [127:0] array [15:0];
   wire [127:0] mux_array [3:0];
   
   //genvar i;
   //generate
   //for(i=0;i<16;i=i+1)
   //  begin : generate_loop
   //  //Allowed since i is constant when the loop is unrolled
   //  assign array[i] = {Din_high[127-i*8:0], Din_low[127:127-i*8]};
   //  end
   //    endgenerate
   
   assign array[0] = {Din_high[127:0]};
   assign array[1] = {Din_high[119:0], Din_low[127:120]};
   assign array[2] = {Din_high[111:0], Din_low[127:112]};
   assign array[3] = {Din_high[103:0], Din_low[127:104]};
   assign array[4] = {Din_high[95:0], Din_low[127:96]};
   assign array[5] = {Din_high[87:0], Din_low[127:88]};
   assign array[6] = {Din_high[79:0], Din_low[127:80]};
   assign array[7] = {Din_high[71:0], Din_low[127:72]};
   assign array[8] = {Din_high[63:0], Din_low[127:64]};
   assign array[9] = {Din_high[55:0], Din_low[127:56]};
   assign array[10] = {Din_high[47:0], Din_low[127:48]};
   assign array[11] = {Din_high[39:0], Din_low[127:40]};
   assign array[12] = {Din_high[31:0], Din_low[127:32]};
   assign array[13] = {Din_high[23:0], Din_low[127:24]};
   assign array[14] = {Din_high[15:0], Din_low[127:16]};
   assign array[15] = {Din_high[7:0], Din_low[127:8]};
   
   //muxes to select shifted value, first round of muxes
   mux4_128 mux1 (mux_array[0],array[0],array[1],array[2],array[3],amnt[0],amnt[1]);
   mux4_128 mux2 (mux_array[1],array[4],array[5],array[6],array[7],amnt[0],amnt[1]);
   mux4_128 mux3 (mux_array[2],array[8],array[9],array[10],array[11],amnt[0],amnt[1]);
   mux4_128 mux4 (mux_array[3],array[12],array[13],array[14],array[15],amnt[0],amnt[1]);
   
   //last round of muxes
   mux4_128 mux5 (Dout,mux_array[0],mux_array[1],mux_array[2],mux_array[3],amnt[2],amnt[3]);
	
endmodule

