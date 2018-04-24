`define cycle 100
`define error_time 1.0
`define runtime #2000

module TOP;
   //ALU inputs
   reg [31:0] a, b;
   reg carry_in;

   wire [31:0] result;
   wire carry_out;
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
            if(result != (a << b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            a = 32'hffffffff;
            b = 32'h00000002;
         #`cycle //3
            if(result != (a << b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            a = 32'hbcdabcda;
            b = 32'h00000003;
         #`cycle //5
            if(result != (a << b)) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            a = 32'h96579657;
            b = 32'h00000004;
         #`cycle //7
            if(result != (a << b)) 
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
	 $vcdplusfile("shifter.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   
   always @(*)
      if(error == 1)
      $strobe ("time: %0d found error at: a = %x, b = %x, recieved result = %x, correct result = %x", 
          $time, a, b, result, (a << b));
      else
      $strobe ("correct: time: %0d: a = %x, b = %x, result = %x", 
          $time, a, b, result);

      shift_arithmetic_left_w_carry u_shift_arithmetic_left_w_carry(
         result, carry_out, a, b);

endmodule
