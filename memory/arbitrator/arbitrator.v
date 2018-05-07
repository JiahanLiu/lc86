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

   dff8$ state_reg(BUS_CLK, next_state, current_state, , CLR, PRE);

   wire                        REQ, DONE;

   or1_6way req_u(REQ, BR[0], BR[1], BR[2], BR[3], BR[4], BR[5]);

   inv1$ req_b_u(REQ_BAR, REQ);

   assign next_state[1] = REQ;

   nor3$ idle_state(next_state[0], REQ, current_state[0], current_state[1]);
 



     //GENERATE CONTROL SIGNALS
   wire                        switch_master;

   wire                        clr_master;

   wire [7:0] 		       new_master;

   wire                        busy_switch, idle_2busy;

   and3$ busy_u(busy_switch, current_state[1], REQ, DONE);

   and2$ idle_u(idle_2busy, current_state[0], REQ_BAR);

   or2$ switch_u(switch_master, busy_switch, idle_2busy);

   assign clr_master = REQ_BAR;

      //TODO actually generate new_master value


      //REGISTERS FOR THE ARBITRATOR
   wire [7:0] 		       current_master, next_master;

   wire 		       mstr_clr;
   pick_master(next_master, BR);
   
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








