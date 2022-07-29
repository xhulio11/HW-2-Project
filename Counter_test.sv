`timescale 1us/1ns

module Counter_test;
	logic [15:0]data_in;
	logic rst_,ld_cnt,updn_cnt,count_enb,clk;
	logic [15:0]data_out;
	
	Counter counter (data_in,rst_,ld_cnt,updn_cnt,count_enb,clk,data_out);
	
	bind Counter Counter_assertions binded(data_in,rst_,ld_cnt,updn_cnt,count_enb,clk,data_out);
	
	always #10 clk = ~ clk;
	
	initial begin
		clk = 0;
		data_in = 10;
		rst_ = 0;
		ld_cnt = 1;
		updn_cnt = 1;
		count_enb = 1;
		
		#29;
		data_in = 5;
		rst_ = 1;
		ld_cnt = 0;
		updn_cnt = 1;
		count_enb = 1;
    @(posedge clk);
		
		#19
	    data_in = 10;
		rst_ = 1;
		ld_cnt = 1;
		updn_cnt = 1;
		count_enb = 1;
	@(posedge clk);

		#19
		data_in = 7;
		rst_ = 1;
		ld_cnt = 1;
		updn_cnt = 1;
		count_enb = 1;
		
	@(posedge clk);

		#19
		data_in = 7;
		rst_ = 0;
		ld_cnt = 1;
		updn_cnt = 0;
		count_enb = 1;
		
	@(posedge clk);

		#19
		data_in = 10;
		rst_ = 1;
		ld_cnt = 0;
		updn_cnt = 0;
		count_enb = 1;
	@(posedge clk);

		#19
		data_in = 7;
		rst_ = 1;
		ld_cnt = 1;
		updn_cnt = 0;
		count_enb = 1;
	@(posedge clk);

		#19
		data_in = 7;
		rst_ = 1;
		ld_cnt = 1;
		updn_cnt = 0;
		count_enb = 0;
	@(posedge clk);

		#19
		data_in = 7;
		rst_ = 1;
		ld_cnt = 1;
		updn_cnt = 0;
		count_enb = 0;
	end 
endmodule 