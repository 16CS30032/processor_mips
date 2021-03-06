`timescale 1ns / 1ps
// S. SASI BHUSHAN 16CS30032
//K. SAI SURYA TEJA 16CS30015
//GRP - 46
////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   20:31:58 11/03/2018
// Design Name:   main_module
// Module Name:   /home/sasi/Desktop/asgn7_coa/test_main.v
// Project Name:  asgn7_coa
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: main_module
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module test_main;

	// Inputs
	reg clk;
	reg reset;

	// Outputs
	wire [31:0] ALU_result;

	// Instantiate the Unit Under Test (UUT)
	main_module uut (
		.clk(clk), 
		.reset(reset), 
		.ALU_result(ALU_result)
	);

	initial begin
		// Initialize Inputs
		clk = 0;
		reset = 0;
/*
		// Wait 100 ns for global reset to finish
		#100;
		reset = 1;
		#100;
		reset =0;
		clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;		
        */
		#100;
		reset = 1;
		#99;
		reset =0;
		#1;
		clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		#50 clk = ~clk;
		
	end
      
endmodule

