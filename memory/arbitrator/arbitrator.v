module arbitrator(input BUS_CLK,
		  input CLR, PRE,
		  input [5:0] BR,
		  output [5:0] BG,
		  //The arbitrator unifes all acknowledge signals together
		  input [5:0] CNTRLR_ACK,
		  output BUS_ACK);

      //NEXT STATE LOGIC
   parameter IDLE = 8'b0000_0001, BUSY = 8'b0000_0010;

   wire [7:0] 		       current_state, next_state;
   assign next_state[7:2] = 0;
   dff8$ state_reg(BUS_CLK, next_state, current_state, , CLR, PRE);

   wire                        REQ;

   or1_6way req_u(REQ, BR[0], BR[1], BR[2], BR[3], BR[4], BR[5]);

   inv1$ req_b_u(REQ_BAR, REQ);

   assign next_state[1] = REQ;

   nor2$ idle_state(next_state[0], REQ, current_state[1]);
 



     //GENERATE CONTROL SIGNALS
   wire                        switch_master;
   wire                        clr_master;
   wire                        busy_switch, idle_2busy;
   wire 		       DONE;
   //generating if current master is done
   wire [5:0]		       BR_BG_MASK;
   wire 		       low_match, high_match;
   and2$ masker [5:0] (BR_BG_MASK, BR, BG);
   or3$ low_u(low_match, BR_BG_MASK[0], BR_BG_MASK[1], BR_BG_MASK[2]);
   or3$ high_u(high_match, BR_BG_MASK[3], BR_BG_MASK[4], BR_BG_MASK[5]);
   or2$ DONE_U(DONE, high_match, low_match);
   
   
   //picking new master signals
   and3$ busy_u(busy_switch, current_state[1], REQ, DONE);

   and2$ idle_u(idle_2busy, current_state[0], REQ);

   or2$ switch_u(switch_master, busy_switch, idle_2busy);

   assign clr_master = REQ_BAR;


      //REGISTERS FOR THE ARBITRATOR
   wire [7:0] 		       current_master, next_master, new_master;

   wire 		       mstr_clr;
   pick_master pick_master_u(new_master, BR);
   
   and2$ clr_u(mstr_clr, clr_master, CLR);

   mux2_8$ mstr_sel(next_master, current_master, new_master, switch_master);

   dff8$ current_mstr(BUS_CLK, next_master, current_master, , CLR, PRE);
   assign BG = current_master[5:0];
   
   //EASY TASK UNIFYING ALL REQUESTS
   or1_6way ACK_UNIFIER(BUS_ACK, CNTRLR_ACK[0], CNTRLR_ACK[1], CNTRLR_ACK[2],
     CNTRLR_ACK[3], CNTRLR_ACK[4], CNTRLR_ACK[5]);
   


   endmodule // arbitrator
//priority of requests
//MEM is most impt
//Then DCACHE
//THen ICACHE
//then KBD
//then DMA
module  pick_master(output [7:0] next_master,
		    input [5:0] bus_reqs);
   assign next_master[7:3] = 0;
   wire [5:0] 			bus_reqs_bar;
   inv1$ bus_reqs_bar_u [5:0] (bus_reqs_bar, bus_reqs);
   assign next_master[2] = bus_reqs[2];
   and2$ dcache_g(next_master[1], bus_reqs[1], bus_reqs_bar[2]);
   and3$ icache_g(next_master[0], bus_reqs[0], bus_reqs_bar[1], bus_reqs_bar[2]);
   
   


endmodule // pick_master








