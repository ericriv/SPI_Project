
module SPI_master_tb;
	localparam integer SYS_CLK_FREQ = 50_000_000; //Hz
	localparam integer SPI_CLK_FREQ = 10_000_000; //Hz
	localparam logic [1:0] SPI_MODE = 0; //SPI MODE (0,1,2,3)
	localparam integer NUM_CS = 1;
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

	SPI_master #(SYS_CLK_FREQ, SPI_CLK_FREQ, SPI_MODE, NUM_CS, DATA_WIDTH)
		my_spi(.clk, .rst_n, .start, .miso, .tx_data, .slave_id, .sclk, .ready, .mosi,
				.SS_n, .rx_data);
				
	bind SPI_master SPI_master_sva #(SYS_CLK_FREQ, SPI_CLK_FREQ, SPI_MODE, NUM_CS, DATA_WIDTH)
		my_spi_bind(.clk, .rst_n, .start, .miso, .tx_data, .slave_id, .sclk, .ready, .mosi,
				.SS_n, .rx_data);
	
	initial begin
	
	#5
	$stop;
	end 

endmodule