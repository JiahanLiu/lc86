`define cycle 100
`define error_time 1.0
`define runtime #2000

module TOP;
   //ALU inputs
   wire [63:0] out; 
   reg [63:0] MM_A, MM_B;
   reg [31:0] imm; 
   reg [2:0] op;

   wire [63:0] out;

   reg error;
   reg error_free;

   initial
      begin
            error_free = 1;
            error = 0;
            op = 3'b010;
            MM_A = 64'h0000_0000_0000_0082;
            MM_B = 64'h0000_0000_0000_0028;
         #`cycle //1
            $strobe ("time: %0d found error at: a = %x, b = %x, recieved out = %x", 
            $time, MM_A, MM_B, out);
            if(out != 64'h0000_0000_0000_00AA); 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //2
            error = 0;
            MM_A = 64'h0000_0000_0000_7FFF;
            MM_B = 64'h0000_0000_0000_7FFF;
         #`cycle //3
            $strobe ("time: %0d found error at: a = %x, b = %x, recieved out = %x", 
            $time, MM_A, MM_B, out);
            if(out != 64'h0000_0000_0000_7FFF) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //4
            error = 0;
            MM_A = 64'h0000_0000_0000_7FFF;
            MM_B = 64'h0000_0000_0000_0001;
         #`cycle //5
            $strobe ("time: %0d found error at: a = %x, b = %x, recieved out = %x", 
            $time, MM_A, MM_B, out);
            if(out != 64'h0000_0000_0000_7FFF) 
            begin
               error_free = 0;
               error = 1;
            end
         #`error_time //6
            error = 0;
            MM_A = 64'h0000_0000_0000_8001;
            MM_B = 64'h0000_0000_0000_8FF0;
         #`cycle //7
            $strobe ("time: %0d found error at: a = %x, b = %x, recieved out = %x", 
            $time, MM_A, MM_B, out);
            if(out != 64'h0000_0000_0000_8000) 
            begin
               error_free = 0;
               error = 1;
            end
         if(error_free == 1)
            $display("\n*** WOOT! TEST PASS! ***\n");      
      end
    
   initial `runtime $finish;
   
   // Dump all waveforms to d_latch.dump.vpd
   initial
      begin
	 //$dumpfile ("d_latch.dump");
	 //$dumpvars (0, TOP);
	 $vcdplusfile("paddsw.dump.vpd");
	 $vcdpluson(0, TOP); 
      end // initial begin
   /*
   always @(*)
      if(error == 1)
      $strobe ("time: %0d found error at: a = %x, b = %x, recieved out = %x", 
          $time, MM_A, MM_B, out);
      else
      $strobe ("correct: time: %0d: a = %x, b = %x, out = %x", 
          $time, MM_A, MM_B, out);
          */

    alu64 u_alu64(out, MM_A, MM_B, imm, op);

endmodule
