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

localparam integer DIVIDER = SYS_CLK_FREQ / (2 * SPI_CLK_FREQ);


property check_reset;
	@(posedge clk) 
		(!rst_n |-> (`sclk_counter == 0 && `state == SPI_master_tb.my_spi.IDLE && ready && SS_n == {NUM_CS{1'b1}}
					&& rx_data == 0 && `rx_shifter == 0 && `tx_shifter == 0 && `bit_counter == 0 && (sclk == SPI_MODE[1])));
endproperty
check_resetP: assert property (check_reset) else $display($stime,"\t\t FAIL::check_reset\n");
check_resetC: cover property (check_reset) $display($stime,"\t\t PASS::check_reset\n");

property check_idle_clk;
	@(posedge clk) disable iff(!rst_n)
		(`state == SPI_master_tb.my_spi.IDLE |-> sclk == SPI_MODE[1]);
endproperty
check_idle_clkP: assert property (check_idle_clk) else $display($stime,"\t\t Fail::check_idle_clk\n");
check_idle_clkC: cover property (check_idle_clk) $display($stime,"\t\t Pass::check_idle_clk\n");

property check_sample;
	@(posedge clk) disable iff(!rst_n)
		((`state == SPI_master_tb.my_spi.DATA && (($rose(sclk) && !SPI_MODE[0]) || ($fell(sclk) && SPI_MODE[0]))) |-> 
			$stable(miso));
endproperty
check_sampleP: assert property (check_sample) else $display($stime,"\t\t Fail::check_sample\n");
check_sampleC: cover property (check_sample) $display($stime,"\t\t Pass::check_sample\n");

property check_shift;
	@(posedge clk) disable iff(!rst_n)
		((`state == SPI_master_tb.my_spi.DATA && (($rose(sclk) && SPI_MODE[0]) || ($fell(sclk) && !SPI_MODE[0]))) |-> 
			`bit_counter == ($past(`bit_counter) + 1));
endproperty
check_shiftP: assert property (check_shift) else $display($stime,"\t\t Fail::check_shift\n");
check_shiftC: cover property (check_shift) $display($stime,"\t\t Pass::check_shift\n");

property check_sclk_count;
	@(posedge clk) disable iff(!rst_n)
		($fell(ready) |-> ($rose(sclk))[=DATA_WIDTH] ##0 $rose(ready));
endproperty
check_sclk_countP: assert property (check_sclk_count) else $display($stime, "\t\t Fail::check_sclk_count\n");
check_sclk_countC: cover property (check_sclk_count) $display($stime, "\t\t Pass::check_sclk_count\n");

property check_ss_n;
	@(posedge clk) disable iff(!rst_n)
		($fell(ready) |-> ##1 $stable(SS_n) until $rose(ready));
endproperty
check_ss_nP: assert property (check_ss_n) else $display($stime,"\t\t Fail::check_ss_n\n");
check_ss_nC: cover property (check_ss_n) $display($stime,"\t\t Pass::check_ss_n\n");

property check_spi_freq;
  @(posedge clk) disable iff(!rst_n)
		(`state == SPI_master_tb.my_spi.DATA && ($rose(sclk) || $fell(sclk))) |-> 
			(!($rose(sclk) || $fell(sclk)))[*(DIVIDER-1)] ##1 ($rose(sclk) || $fell(sclk));
endproperty
check_spi_freqP: assert property (check_spi_freq) else $display($stime,"\t\t Fail::check_spi_freq\n");
check_spi_freqC: cover property (check_spi_freq) $display($stime,"\t\t Pass::check_spi_freq\n");




/*
check_spi_mode0_C: cover property (@(posedge clk) disable iff(!rst_n) (SPI_MODE == 0)) 
	$display($stime,"\t\t Pass::check_spi_mode0\n");

check_spi_mode1_C: cover property (@(posedge clk) disable iff(!rst_n) (SPI_MODE == 1)) 
	$display($stime,"\t\t Pass::check_spi_mode1\n");
	
check_spi_mode2_C: cover property (@(posedge clk) disable iff(!rst_n) (SPI_MODE == 2)) 
	$display($stime,"\t\t Pass::check_spi_mode2\n");
	
check_spi_mode3_C: cover property (@(posedge clk) disable iff(!rst_n) (SPI_MODE == 3)) 
	$display($stime,"\t\t Pass::check_spi_mode3\n");
*/

check_back_to_back_transfer: cover property (@(posedge clk) disable iff(!rst_n) 
	($rose(ready) |-> ##1 $fell(ready))) $display($stime,"\t\t Pass::check_back_to_back_transfer\n");
	
check_reset_in_transfer: cover property (@(posedge clk) (`state == SPI_master_tb.my_spi.DATA |->
	$fell(rst_n))) $display($stime, "\t\t Pass::check_reset_in_transfer\n");



endmodule 