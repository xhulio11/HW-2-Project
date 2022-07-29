`timescale 1us/1ps

module FIFO_assertions	
		(input int counter,
		 input [3:0]wr_ptr,[3:0]rd_ptr,
		 input [15:0]fifo_data_in,
	     input rst_,fifo_write,fifo_read,clk,
	     input [15:0]fifo_data_out,
	     input fifo_full,fifo_empty);
	

	/*
		--check_reset--
		This property checks if reset is working properly.
		Reset should make writing,reading pointer 0 and inform that FIFO is not full (fifo_full = 0)
		and FIFO is empty (fifo_empty = 1)
	*/
	property check_reset;
		@(negedge rst_) 1'b1 |-> @(posedge clk) (wr_ptr == 0 && rd_ptr == 0 && fifo_full == 0 && fifo_empty == 1);
	endproperty
	
	
	/*
		--check_fifo_empty--
		This property checks if the fifo empty is activated (fifo_empty = 1) when counter = 0
		
	*/
	property check_fifo_empty;
		@(posedge clk) disable iff(!rst_) (counter == 0) |-> (fifo_empty == 1);
	endproperty 
	
	
	/*
		--check_fifo_full--
		This property checks if the fifo_full is activated (fifo_full = 1) when counter = 16
	*/
	property check_fifo_full;
		@(posedge clk) disable iff(!rst_) (counter == 16) |-> (fifo_full == 1);
	endproperty
	
	
	/*
		--check_write_pointer--
		This property checks if writing pointer stays stable when the counter = 16 => FIFO is full 
	*/
	property check_write_pointer;
		@(posedge clk) disable iff(!rst_) (counter == 16 && fifo_write && !fifo_read) |=> $stable(wr_ptr);
	endproperty
	
	
	/*
		--check_read_pointer--
		This property checks if reading pointer stays stabel when the counter = 0 => FIFO is empty
	*/
	property check_read_pointer;
		@(posedge clk) disable iff(!rst_) (counter == 0 && !fifo_write && fifo_read) |=> $stable(rd_ptr);
	endproperty
	
	
	// ASSERTING PROPERTIES
	control_reset: assert property (check_reset) $display("1-PASS: RESET WORKS %t\n",$time);
					else $display("1-FAIL: RESET DOES NOT WORK %t\n",$time);

	control_fifo_empty: assert property (check_fifo_empty) $display("2-PASS: FIFO EMPTY WORKS %t\n",$time);
						else $display("2-FAIL: FIFO EMPTY DOES NOT WORK %t\n",$time);
						
	control_check_fifo_full: assert property (check_fifo_full) $display("3-PASS: FIFO FULL WORKS %t\n",$time);
						else $display("3-FAIL: FIFO FULL DOES NOT WORK %t \n",$time);
						
	control_check_write_pointer: assert property(check_write_pointer) $display("4-PASS: WRITE POINTER WORKS %t\n",$time);
								else $display("4-FAIL: WRITE POINTER DOES NOT WORK %t\n",$time);
	
	control_chekc_read_pointer: assert property(check_read_pointer) $display("5-PASS: READ POINTER WORKS %t\n",$time);
								else $display("5-FAIL: READ POINTER DOES NOT WORK %t\n",$time);

endmodule 