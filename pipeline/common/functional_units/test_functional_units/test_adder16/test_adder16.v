`define cycle 4.2
`define error_time 1.0
`define runtime #2000

module TOP;
   //ALU inputs
   reg [15:0] a, b;
   reg carry_in;

   wire [15:0] sum;
   wire [15:0] carry_out;

   reg error;
   reg error_free;

   initial
      begin
            error_free = 1;
            error = 0;
            a = 16'hfffe;
            b = 16'h0001;
         #`cycle //1
            if(sum != (a + b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            a = 16'h1723;
            b = 16'h8323;
         #`cycle //3
            if(sum != (a + b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            a = 16'hbcda;
            b = 16'h7986;
         #`cycle //5
            if(sum != (a + b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            a = 16'h9657;
            b = 16'h3456;
         #`cycle //7
            if(sum != (a + b)) 
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

    adder16 u_adder16(sum, carry_out, a, b);
   
endmodule
