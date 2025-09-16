`define state SPI_master_tb.my_spi.state
`define sclk_counter SPI_master_tb.my_spi.sclk_counter
`define bit_counter SPI_master_tb.my_spi.bit_counter
`define rx_shifter SPI_master_tb.my_spi.rx_shifter
`define tx_shifter SPI_master_tb.my_spi.tx_shifter

module SPI_master_sva #(
parameter integer SYS_CLK_FREQ = 50_000_000, //Hz
parameter integer SPI_CLK_FREQ = 10_000_000, //Hz
parameter logic [1:0] SPI_MODE = 0, //SPI MODE (0,1,2,3)
parameter integer NUM_CS = 1,
parameter integer DATA_WIDTH = 8
)(
input	logic							clk,
input	logic							rst_n,
input	logic							start,
input	logic							miso,
input	logic	[DATA_WIDTH-1:0]		tx_data,
input	logic	[$clog2(NUM_CS)-1:0]	slave_id,
input	logic							sclk,
input	logic							ready,
input	logic							mosi,
input	logic	[NUM_CS-1:0]			SS_n,
input	logic	[DATA_WIDTH-1:0]		rx_data
);


property check_reset;
	@(posedge clk) 
		(!rst_n |-> (`sclk_counter == 0 && `state == SPI_master_tb.my_spi.IDLE && ready && SS_n == {NUM_CS{1'b1}}
					&& rx_data == 0 && `rx_shifter == 0 && `tx_shifter == 0 && (sclk == SPI_MODE[1])));
endproperty
check_resetP: assert property (check_reset) else $display($stime,"\t\t FAIL::check_reset\n");
check_resetC: cover property (check_reset) $display($stime,"\t\t PASS::check_reset\n");


endmodule 