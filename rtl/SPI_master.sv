
module SPI_master #(
parameter integer SYS_CLK_FREQ = 50_000_000, //Hz
parameter integer SPI_CLK_FREQ = 10_000_000, //Hz
parameter logic [1:0] SPI_MODE = 0, //SPI MODE (0,1,2,3)
parameter integer SLAVE_LINES = 1
)(
input	logic						clk,
input	logic						rst_n,
output	logic						sclk,
output	logic	[SLAVE_LINES-1:0]	SS_n
);

	localparam integer DIVIDER = SYS_CLK_FREQ / (2 * SPI_CLK_FREQ);

	logic	[$clog2(DIVIDER)-1:0]	sclk_counter;

	always @(posedge clk || negedge rst_n) begin
	
		if(!rst_n) begin
			sclk_counter <= 0;
			sclk <= (SPI_MODE == 2'b10) ? 1'b1 : 1'b0; //sclk idle is high only in MODE 2
		end //rst_n
		
		else begin
		
		end
	
	end 

endmodule 