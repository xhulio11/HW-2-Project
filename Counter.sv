`timescale 10us/10ps

module Counter
   (input [15:0]data_in,
	input rst_,ld_cnt,updn_cnt,count_enb,clk,
	output logic [15:0]data_out);
	
	logic [15:0] data;
	
	always_ff @(posedge clk,negedge rst_) begin
		
		priority if (!rst_) data = 0;
		
		else if (!ld_cnt) data = data_in;
		
		else if(count_enb)begin
			if(updn_cnt) data = data + 1;
			else data = data - 1;
		end else data = data;
	end
	
	assign data_out = data;
	
endmodule


