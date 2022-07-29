`timescale 1us/1ns

module Counter_assertions 
   (input [15:0]data_in,
	input rst_,ld_cnt,updn_cnt,count_enb,clk,
	input [15:0]data_out);
	
	
	/*
		--check_reset--
		This property when it is asserted checks if reset=0 (active low)
		makes output 0 in the next positive clock edge
			
	*/
	property check_reset;
		@(negedge rst_) 1'b1 |-> @(posedge clk)(data_out == 16'd0);
	endproperty


	/*
		--check_output--
		This property when it is asserted checks if ld_cnt=1 (active low) and count_enb=1 (active high)
		make output stay stable for continous cycles 
	*/
	property check_output;
		@(posedge clk) disable iff(!rst_) (ld_cnt && !count_enb)|=> $stable(data_out);
	endproperty


	/*
		--check_increment--
		--check_decrements--
		Tis property when it is asserted checks if ld_cnt=1 (active low) and count_enb=1(active high)
		make output increases or decreases according to updn_cnt(high-> increase, low->decrease). 
	*/

	property check_increment;
		@(posedge clk) disable iff(!rst_) (ld_cnt && count_enb && updn_cnt)|=> ($past(data_out)+1 == data_out);
	endproperty
	
	property check_dincrement;
		@(posedge clk)  disable iff(!rst_) (ld_cnt && count_enb && !updn_cnt)|=> ($past(data_out,1) == data_out+1);
	endproperty

		
	// ASSERTING PROPERTIES
	control_reset: assert property (check_reset) $display("1-PASS: RESET WORKS %t\n",$time);
					else $display("1-FAIL: RESET DOES NOT WORK\n %t\n",$time);

	control_ouput: assert property (check_output) $display("2-PASS: STABLE OUTPUT WORKS %t\n",$time);
					else $display("2-FAIL: STABLE OUTPUT DOES NOT WORK %t\n",$time);

	control_increment: assert property (check_increment) $display("3-PASS: INCREMENT WORKS %t\n",$time);
					else $display("3-FAIL:INCREMENT DOES NOT WORK %t\n",$time);

	control_dincrement: assert property (check_dincrement) $display("4-PASS: DINCREMENT WORKS %t\n",$time);
					else $display("4-FAIL:DINCREMENT DOES NOT WORK %t\n",$time);



endmodule