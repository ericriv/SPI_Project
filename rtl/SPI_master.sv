
module SPI_master #(
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
output	logic							sclk,
output	logic							ready,
output	logic							mosi,
output	logic	[NUM_CS-1:0]			SS_n,
output	logic	[DATA_WIDTH-1:0]		rx_data
);

	localparam integer DIVIDER = SYS_CLK_FREQ / (2 * SPI_CLK_FREQ);
	
	typedef enum {IDLE, DATA} state_t;
	state_t state;

	logic	[$clog2(DIVIDER)-1:0]		sclk_counter;
	logic	[$clog2(DATA_WIDTH):0]	bit_counter;
	logic	[DATA_WIDTH-1:0]			rx_shifter;
	logic	[DATA_WIDTH-1:0]			tx_shifter;

	always @(posedge clk or negedge rst_n) begin //system clock procedural block
	
		if(!rst_n) begin
			sclk_counter <= 0;
			bit_counter <= 0;
			state <= IDLE;
			ready <= 1'b1;
			SS_n <= {NUM_CS{1'b1}};
			rx_data <= {DATA_WIDTH{1'b0}};
			rx_shifter <= {DATA_WIDTH{1'b0}};
			tx_shifter <= {DATA_WIDTH{1'b0}};
			sclk <= (SPI_MODE[1] == 1'b1) ? 1'b1 : 1'b0; //sclk idle is high in MODE 2 & 3
		end //rst_n
		
		else begin
			case(state)
				IDLE: begin
					sclk_counter <= 0;
					bit_counter <= 0;
					if(start) begin
						state <= DATA;
						ready <= 1'b0;
						tx_shifter <= tx_data;
						SS_n <= ~(1 << slave_id);
					end
					else
						state <= IDLE;
				end //IDLE
				
				DATA: begin
					if(sclk_counter == DIVIDER-1) begin
						sclk <= ~sclk;
						sclk_counter <= 0;
					end
					else begin
						sclk_counter <= sclk_counter + 1;
					end
					state <= DATA;
				end //DATA
				
				default: begin
					state <= state;
				end //defualt
			endcase
		end
	
	end 
	
	always @(posedge sclk) begin    
		if(SPI_MODE[0] == 1'b0) begin //sample for MODE 0 and 2
			rx_shifter <= {rx_shifter[DATA_WIDTH-2:0], miso};
			bit_counter <= bit_counter + 1'b1;
		end
		else begin //shift for MODE 1 and 3
			tx_shifter <= {tx_shifter[DATA_WIDTH-2:0], 1'b0};
			if(bit_counter == DATA_WIDTH) begin
				state <= IDLE;
				rx_data <= rx_shifter;
				SS_n <= {NUM_CS{1'b1}};
				ready <= 1'b1;
			end
		end
	end
	
	always @(negedge sclk) begin   
		if(SPI_MODE[0] == 1'b1) begin //sample for MODE 1 and 3
			rx_shifter <= {rx_shifter[DATA_WIDTH-2:0], miso};
			bit_counter <= bit_counter + 1'b1;
		end
		else begin  //shift for MODE 0 and 2
			tx_shifter <= {tx_shifter[DATA_WIDTH-2:0], 1'b0};
			if(bit_counter == DATA_WIDTH) begin
				state <= IDLE;
				rx_data <= rx_shifter;
				SS_n <= {NUM_CS{1'b1}};
				ready <= 1'b1;
			end
		end
	end
	
	assign mosi = tx_shifter[DATA_WIDTH-1];

endmodule 