`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 12/03/2024 12:37:47 PM
// Design Name: 
// Module Name: Interface
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

interface VecAluInt #(parameter D_BUS_WIDTH = 4, parameter REG_FLAGS_WIDTH = 6, parameter OPCODE_WIDTH = 4, parameter TOTAL_OF_ALUS = 8) ();
    logic [((REG_FLAGS_WIDTH * TOTAL_OF_ALUS) - 1):0] SIGNALS;
    logic [((D_BUS_WIDTH * TOTAL_OF_ALUS) - 1):0] Z;          
    logic [((D_BUS_WIDTH * TOTAL_OF_ALUS) - 1):0] A;
    logic [((D_BUS_WIDTH * TOTAL_OF_ALUS) - 1):0] B;
    logic [(OPCODE_WIDTH - 1):0] SEL;                               
    logic [(TOTAL_OF_ALUS - 1):0]ENABLE;                                                                       
    logic [(TOTAL_OF_ALUS - 1):0]RST;

    localparam ZERO_VALUE = 0;
    localparam MAX_VALUE = (2**D_BUS_WIDTH) - 1;   // MAX_VALUE = 15
    localparam MIDDLE_VALUE = ((MAX_VALUE - 0) / 2) + 0;     // MIDDLE_VALUE = 7
    localparam TOTAL_OF_OPERATIONS = 10;
    
    bit [(D_BUS_WIDTH - 1):0] a;
    bit [(D_BUS_WIDTH - 1):0] b;
    
    
    //////////////////////////////// BFM ////////////////////////////////
    
    // Function that reset the ALU "N"
    function reset_ALU_N(integer ALU_N, input bit state);
        RST[(ALU_N - 1)] = 1;
        RST[(ALU_N - 1)] = 0;
        RST[(ALU_N - 1)] = 1;
    endfunction
    
    // Function to set the state of the input "ENABLE" of the correspond ALU "N".
    function set_input_ENABLE_to_state(integer ALU_N, input bit state);
        ENABLE[(ALU_N - 1)] = state;
    endfunction
	
	// Function to set the state of the input "ENABLE" for all ALUS to 1																							 
    function set_all_ALUS_ENABLE_to_state(input bit state);
        ENABLE = {TOTAL_OF_ALUS{state}};
    endfunction
	
	// Function to set the state of the input "RST" of the correspond ALU "N".
    function set_input_RST_to_state(integer ALU_N, input bit state);
        RST[(ALU_N - 1)] = state;
    endfunction
	
	// Function to set the state of the input "RST" for all ALUS to 1																							 
    function set_all_ALUS_RST_to_state(input bit state);
        RST = {TOTAL_OF_ALUS{state}};
    endfunction
 
															   
														
									 
					
   
    // Function to set the value of the input "A" to zero
    function set_input_A_to_zero();
        a = 0;
        A = {TOTAL_OF_ALUS{a}};
    endfunction
    
    // Function to set the value of the input "B" to zero
    function set_input_B_to_zero();
        b = 0;
        B = {TOTAL_OF_ALUS{b}};
    endfunction
    
    // Function to set the value of the inputs "A" and "B" to zero
    function set_input_A_and_B_to_zero();
        a = 0;
        b = 0;
        A = {TOTAL_OF_ALUS{a}};
        B = {TOTAL_OF_ALUS{b}};
    endfunction

    // Function to set the value of the input "A" to the maximum value
    function set_input_A_to_max_value();
        a = MAX_VALUE;
        A = {TOTAL_OF_ALUS{a}};
    endfunction
    
    // Function to set the value of the input "B" to the maximum value
    function set_input_B_to_max_value();
        b = MAX_VALUE;
        B = {TOTAL_OF_ALUS{b}};
    endfunction
    
    // Function to set the value of the inputs "A" and "B" to the maximum value
    function set_input_A_and_B_to_max_value();
        a = MAX_VALUE;
        b = MAX_VALUE;
        A = {TOTAL_OF_ALUS{a}};
        B = {TOTAL_OF_ALUS{b}};
    endfunction
    
    // Function to randomize input "A"
    function randomize_input_A();
        std::randomize(a);
        A = {TOTAL_OF_ALUS{a}};
    endfunction
 
							  
								   
							   
			   
 
							   
								   
							   
			   
    
    // Function to randomize input "B"
    function randomize_input_B();
        std::randomize(b);
        B = {TOTAL_OF_ALUS{b}};
    endfunction
    
    // Function to randomize input "A" distinct to zero
    function randomize_input_A_distinct_to_zero();
        std::randomize(a) with {a != 0;};
        A = {TOTAL_OF_ALUS{a}};
    endfunction
    
    // Function to randomize input "B" distinct to zero
    function randomize_input_B_distinct_to_zero();
        std::randomize(b) with {b != 0;};
        B = {TOTAL_OF_ALUS{b}};
    endfunction

    // Function that randomize the value of the input SEL.
    function randomize_input_SEL();
        std::randomize(SEL) with {SEL < TOTAL_OF_OPERATIONS;};
    endfunction
    
    // Function to set the value of the input "a" with the value "this_value" 
    function set_input_A_to_value(input logic [(D_BUS_WIDTH - 1): 0] this_value);
        A = {TOTAL_OF_ALUS{this_value}};
    endfunction

    // Function to set the value of the input "b" with the value "this_value" 
    function set_input_B_to_value(input logic [(D_BUS_WIDTH - 1): 0] this_value);
        B = {TOTAL_OF_ALUS{this_value}};
    endfunction
    
																								  
										   
										  
			   

																								  
										   
										  
			   
	
    // Function to randomize input A with values > MIDDLE_VALUE and randomize input B with values > A
    function randomize_inputs_A_and_B_to_generate_overflow();
        std::randomize(a, b) with {a > MIDDLE_VALUE; b > a;};
        A = {TOTAL_OF_ALUS{a}};
        B = {TOTAL_OF_ALUS{b}};
    endfunction
    
    // Function to randomize input B with values > MIDDLE_VALUE and randomize input A with values > B
    function randomize_inputs_B_and_A_to_generate_overflow();
        std::randomize(a, b) with {b > MIDDLE_VALUE; a > b;};
        A = {TOTAL_OF_ALUS{a}};
        B = {TOTAL_OF_ALUS{b}};
    endfunction
    
    // Function to randomize input A with values > MIDDLE_VALUE and randomize input B with values > A
    function randomize_inputs_A_and_B_to_generate_underflow();
        std::randomize(a, b) with {a < b;};
        A = {TOTAL_OF_ALUS{a}};
        B = {TOTAL_OF_ALUS{b}};
    endfunction
 			   
			   
 
    
    function void set_operation_to(string OPERATION);                                        
        case(OPERATION)
            "ADDITION"          : SEL = 0;
            "SUBTRACTION"       : SEL = 1;
            "BITWISE_AND"       : SEL = 2;
            "BITWISE_OR"        : SEL = 3;
            "BITWISE_XOR"       : SEL = 4;
            "COMPARISON"        : SEL = 5;
										  
										  
            "MULTIPLICATION"    : SEL = 8;
            "DIVISION"          : SEL = 9;
            default             : SEL = 0;
        endcase
    endfunction
    
endinterface: VecAluInt
