`timescale 1us/1ps

module FIFO
	(input [15:0]fifo_data_in,
	 input rst_,fifo_write,fifo_read,clk,
	 output logic [15:0]fifo_data_out,
	 output logic fifo_full,fifo_empty);
	
	/*
		WIDTH -> How bits of each memory slot
		DEPTH -> How many memory slots memory has in total
		MSB_ptr-> Which is the most significant bit of the pointer 
	*/
	parameter WIDTH = 16,
			  DEPTH = 16,
			  MSB_ptr = 4;
			  

	/*
		Memory: 16bit x 16 slots memory
		wr_ptr: Writing pointer in memory
		rd_ptr: Reading pointer in memory
		data: Temprary variable for data that must be an output
		counter: a viarable that is used to determine if FIFO is full or not
	*/
	logic [WIDTH-1:0]Memory[DEPTH-1:0];
	logic [MSB_ptr - 1:0]wr_ptr,rd_ptr;
	logic [WIDTH - 1:0]data;
	int counter; 
	
	
	always_ff @(posedge clk,negedge rst_)begin: loop
		priority if (!rst_)begin                 // Reseting circuit
			wr_ptr = 0;
			rd_ptr = 0;
			fifo_full = 0;
			fifo_empty = 1;
			data = 0;
			counter = 0;
		
		end else if (fifo_write)begin            // If fifo_write is TRUE
			if(counter < DEPTH)begin             // If FIFO is not full 
				Memory[wr_ptr] = fifo_data_in;   // Writing data_input in the proper address
				counter++;                       
				wr_ptr++;
				fifo_empty = 0;				     // If at least one element is added, FIFO is not empty
				if(counter == 16)fifo_full = 1;  // If counter == 16 then fifo is FULL
			end else begin 
				fifo_full = 1;                   // else FIFO is full 
				fifo_empty = 0;             
			end 
		
		end else if (fifo_read)begin             // If fifo_read is TRUE
			if(counter > 0)begin                 // If FIFO is not empty
				data = Memory[rd_ptr];           // Reading data_ouput from the proper address 
				rd_ptr++;
				counter--;
				fifo_full = 0;    				 // if at least one element is taken, FIFO is not full
				if (counter == 0)fifo_empty = 1; // If counter == 0 then FIFO is empty
			end else begin 
				fifo_empty = 1;                  // else FIFO is empty
				fifo_full = 0; 
			end 
		end 

	end: loop 
	
	assign fifo_data_out = data; 

endmodule 















