`define cycle 4.2
`define error_time 1.0
`define runtime #2000

module TOP;
   //ALU inputs
   reg [31:0] a, b;
   reg carry_in;

   wire [31:0] sum;
   wire [31:0] sum_w_carry;
   wire [31:0] carry_out;
   wire [31:0] carry_out_w_carry;

   reg error;
   reg error_free;

   initial
      begin
            carry_in = 1;
            error_free = 1;
            error = 0;
            a = 32'hffffffff;
            b = 32'h00000001;
         #`cycle //1
            if(sum != (a + b) || sum_w_carry != (a + b + 1)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            a = 32'hffffffff;
            b = 32'h00000000;
         #`cycle //3
            if(sum != (a + b) || sum_w_carry != (a + b + 1)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            a = 32'hbcdabcda;
            b = 32'h79867986;
         #`cycle //5
            if(sum != (a + b) || sum_w_carry != (a + b + 1)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            a = 32'h96579657;
            b = 32'h34563456;
         #`cycle //7
            if(sum != (a + b) || sum_w_carry != (a + b + 1)) 
            begin
               error_free = 0;
               error = 1;
            end
         if(error_free == 1)
            $display("\n*** WOOT! TEST PASS! %3.2F ns cycle time ***\n", `cycle);      
      end
    
   initial `runtime $finish;
   
   // Dump all waveforms to d_latch.dump.vpd
   initial
      begin
	 //$dumpfile ("d_latch.dump");
	 //$dumpvars (0, TOP);
	 $vcdplusfile("adder.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(*)
      if(error == 1)
      $strobe ("time: %0d found error at: a = %x, b = %x, recieved sum = %x, correct sum = %x", 
          $time, a, b, sum, (a + b));
      else
      $strobe ("correct: time: %0d: a = %x, b = %x, sum = %x", 
          $time, a, b, sum);

    adder32 u_adder32 (sum, carry_out, a, b);
    adder32_w_carry_in u_adder32_w_carry_in (sum_w_carry, carry_out_w_carry, a, b, carry_in);
   
endmodule
