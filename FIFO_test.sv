`timescale 1us/1ps

module FIFO_test;

	logic [15:0]fifo_data_in;
	logic rst_,fifo_write,fifo_read,clk;
	logic [15:0]fifo_data_out;
	logic fifo_full,fifo_empty;
	
	int counter;
	logic [15:0]write_pointer;
	logic [15:0]read_pointer;
	
	assign counter = fifo.counter; 
	assign write_pointer = fifo.wr_ptr;
	assign read_pointer = fifo.rd_ptr;
	
	FIFO fifo(fifo_data_in,rst_,fifo_write,fifo_read,clk,fifo_data_out,fifo_full,fifo_empty);
	
	bind fifo FIFO_assertions binded(fifo.counter,fifo.wr_ptr,fifo.rd_ptr,fifo_data_in,rst_,fifo_write,fifo_read,clk,fifo_data_out,fifo_full,fifo_empty);
	always #10 clk = ~clk;
	
	initial begin
		clk = 0;
		rst_ = 0;
		fifo_write = 1;
		fifo_read = 1;
		fifo_data_in = 123214;
		
		#29               // WRITING 
		rst_ = 1;
		fifo_write = 1;
		fifo_read = 0;
		fifo_data_in = 1;
		@(posedge clk);
		
		#19               // WRITING 
		fifo_write = 1;
		fifo_read = 0;
		fifo_data_in = 2;
		@(posedge clk);
		
		#19               // WRITING 
		fifo_write = 1;
		fifo_read = 0;
		fifo_data_in = 3;
		@(posedge clk);
		
		#19                // READING 
		fifo_write = 0;
		fifo_read = 1;
		fifo_data_in = 2;
		@(posedge clk);
		
		#19                // READING 
		fifo_write = 0;
		fifo_read = 1;
		fifo_data_in = 2;
		@(posedge clk);
		
		#19                // RESETING 
		rst_ = 0;
		fifo_write = 1;
		fifo_read = 1;
		fifo_data_in = 123214;
		@(posedge clk);	
		
		#19		           // WRITING 
		rst_ = 1;
		fifo_write = 1;
		fifo_read = 0;
		fifo_data_in = 10;
		@(posedge clk);
		
		#19                // WRITING
		fifo_write = 1;
		fifo_read = 0;
		fifo_data_in = 11;
		@(posedge clk);
		
		#19                // READING
		fifo_write = 0;
		fifo_read = 1;
		fifo_data_in = 11;
		@(posedge clk);
		
		#19
		fifo_write = 0;
		fifo_read = 1;
		@(posedge clk);
		
		// This loop is used to full FIFO 
		for(int i = 0; i < 20; i++)begin
			#19
			fifo_write = 1;
			fifo_read = 0;
			fifo_data_in = i;
			@(posedge clk);
		end 
		
		// This loop is used to empty FIFO 
		for(int i = 0; i < 20; i++)begin
			#19
			fifo_write = 0;
			fifo_read = 1;
			fifo_data_in = i;
			@(posedge clk);
		end 
		
	end
endmodule 