`timescale 1ns/1ps

module SPI_master_tb;
	localparam integer SYS_CLK_FREQ = 50_000_000; //Hz
	localparam integer SPI_CLK_FREQ = 5_000_000; //Hz
	localparam integer NUM_CS = 1;
	localparam logic [1:0] SPI_MODE = 0; //SPI MODE (0,1,2,3)
	localparam integer DATA_WIDTH = 8;

	logic							clk;
	logic							rst_n;
	logic							start;
	logic							miso;
	logic	[DATA_WIDTH-1:0]		tx_data;
	logic	[$clog2(NUM_CS)-1:0]	slave_id;
	
	wire							sclk;
	wire							ready;
	wire							mosi;
	wire	[NUM_CS-1:0]			SS_n;
	wire	[DATA_WIDTH-1:0]		rx_data;
	
	logic [DATA_WIDTH-1:0]	mosi_ref;
	
	localparam integer DIVIDER = SYS_CLK_FREQ / (2 * SPI_CLK_FREQ);
	

	SPI_master #(SYS_CLK_FREQ, SPI_CLK_FREQ, SPI_MODE, NUM_CS, DATA_WIDTH)
		my_spi(.clk, .rst_n, .start, .miso, .tx_data, .slave_id, .sclk, .ready, .mosi,
				.SS_n, .rx_data);
				
	bind SPI_master SPI_master_sva #(SYS_CLK_FREQ, SPI_CLK_FREQ, SPI_MODE, NUM_CS, DATA_WIDTH)
		my_spi_bind(.clk, .rst_n, .start, .miso, .tx_data, .slave_id, .sclk, .ready, .mosi,
				.SS_n, .rx_data);
	
	initial begin
	$display("Divider = %d",DIVIDER);
	clk = 0;
	reset_spi;
	spi_run(8'h11, 8'h11);
	//spi_run_rand(5);
	//spi_run_rst;
	//spi_run_rand(5);
	#20
	$stop;
	end 
	
	always
	#10 clk = ~clk;
	
	
	//===================//
	// task declarations //
	//===================//
	
	task automatic reset_spi;
		@(negedge clk)
		rst_n = 1;
		start = 0;
		miso = 0;
		tx_data = 0;
		slave_id = 0;
		@(negedge clk) rst_n = 0;
		repeat(2) @(negedge clk);
		rst_n = 1;
	endtask
	
	task automatic spi_run(input logic [DATA_WIDTH-1:0] mosi_val,
								 logic [DATA_WIDTH-1:0] miso_val);
		@(negedge clk)
		tx_data = mosi_val;
		start = 1;
		miso = miso_val[DATA_WIDTH-1];
		@(negedge clk)
		start = 0;
		for(int i = 0; i < DATA_WIDTH; i++) begin
			if(SPI_MODE == 0 || SPI_MODE == 3) begin
				@(posedge sclk)
				mosi_ref[DATA_WIDTH-1-i] = mosi;

				@(negedge sclk)
				if(i != DATA_WIDTH-1)
					miso = miso_val[DATA_WIDTH-2-i];
			end
			else begin
				@(posedge sclk)
				mosi_ref[DATA_WIDTH-1-i] = mosi;
				@(negedge sclk)
				if(i != DATA_WIDTH-1)
					miso = miso_val[DATA_WIDTH-2-i];
			end
		end
		@(negedge clk)
		if(mosi_ref != mosi_val)
			$error("MOSI Scoreboard mismatch! Expected %0b, got %0b", mosi_val, mosi_ref);
		if(rx_data != miso_val)
			$error("MISO Scoreboard mismatch! Expected %0b, got %0b", miso_val, rx_data);
	endtask
	
	task automatic spi_run_rand(input integer num);
		logic [DATA_WIDTH-1:0] mosi_val, miso_val;
		@(negedge clk)
		for(int j = 0; j < num; j++) begin
			mosi_val = $urandom_range(0,{DATA_WIDTH{1'b1}});
			miso_val = $urandom_range(0,{DATA_WIDTH{1'b1}});
			tx_data = mosi_val;
			start = 1;
			miso = miso_val[DATA_WIDTH-1];
			@(negedge clk)
			start = 0;
			for(int i = 0; i < DATA_WIDTH; i++) begin
				if(SPI_MODE == 0 || SPI_MODE == 3) begin
					@(negedge sclk)
					mosi_ref[DATA_WIDTH-1-i] = mosi;
					@(posedge sclk)
					if(i != DATA_WIDTH-1)
						miso = miso_val[DATA_WIDTH-2-i];
				end
				else begin
					@(posedge sclk)
					mosi_ref[DATA_WIDTH-1-i] = mosi;
					@(negedge sclk)
					if(i != DATA_WIDTH-1)
						miso = miso_val[DATA_WIDTH-2-i];
				end
			end
			@(negedge clk)
			if(mosi_ref != mosi_val)
				$error("MOSI Scoreboard mismatch! Expected %0b, got %0b", mosi_val, mosi_ref);
			//else
				//$display("MOSI success %0h = %0h", mosi_val, mosi_ref);
			if(rx_data != miso_val)
				$error("MISO Scoreboard mismatch! Expected %0b, got %0b", miso_val, rx_data);
			//else
				//$display("MISO success %0h = %0h", mosi_val, mosi_ref);
		end
	endtask
	
	task automatic spi_run_rst;
		
		logic [DATA_WIDTH-1:0] mosi_val, miso_val;
		mosi_val = {DATA_WIDTH{1'b1}};
		miso_val = 0;
		@(negedge clk)
		tx_data = mosi_val;
		start = 1;
		miso = miso_val[DATA_WIDTH-1];
		@(negedge clk)
		start = 0;
		for(int i = 0; i < 4; i++) begin
			if(SPI_MODE == 0 || SPI_MODE == 3) begin
				@(negedge sclk)
				mosi_ref[DATA_WIDTH-1-i] = mosi;
				@(posedge sclk)
				if(i != DATA_WIDTH-1)
					miso = miso_val[DATA_WIDTH-2-i];
			end
			else begin
				@(posedge sclk)
				mosi_ref[DATA_WIDTH-1-i] = mosi;
				@(negedge sclk)
				if(i != DATA_WIDTH-1)
					miso = miso_val[DATA_WIDTH-2-i];
			end
		end
		reset_spi;
	endtask
	

endmodule