# ================================
# SPI Simulation Run Script (run.do)
# Run from the sim/ directory
# ================================

# Clean and recreate work directory
#vdel -all
vlib work

# Compile RTL, assertions, and testbench
vlog -sv ../rtl/SPI.sv
vlog -sv ../assertions/SPI_sva.sv
vlog -sv ../tb/SPI_tb.sv

# Run simulation (with limited optimization for waveform viewing)
vsim -voptargs=+acc work.SPI_tb 

# Record sim log
transcript file sim_output.log

# Plot waveform
add wave -r SPI_tb/*

# Run until completion
run -all

#quit -sim
