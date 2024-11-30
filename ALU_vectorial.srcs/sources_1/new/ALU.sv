`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Institution: CINVESTAV Guadalajara Unit
// Engineers: 
// Lino Rosauro González Guerra
// Eduardo Rafael Heredia González
// Emmanuel Díaz Marín
//
// Create Date: 11/20/2024 06:30:01 PM
// Design Name: 
// Module Name: ALU
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


module ALU #(parameter D_BUS_WIDTH = 4, parameter REG_FLAGS_WIDTH = 6, parameter OPCODE_WIDTH = 4)(
    // REG_FLAGS -> Bit 0 = Zero flag, Bit 1 = less flag, Bit 2 = Equal flag, Bit 3 = Greater flag, Bit 4 = Underflow flag, Bit 5 = Overflow flag
    output reg [(REG_FLAGS_WIDTH - 1):0] REG_FLAGS,
    output reg [(D_BUS_WIDTH - 1): 0] RESULT,
    input [(D_BUS_WIDTH - 1): 0] OPERAND_A,
    input [(D_BUS_WIDTH - 1): 0] OPERAND_B,
    input [(OPCODE_WIDTH - 1):0] OPCODE,
    input ENABLE,
    input CLK,
    input ARST
);

  //Local parameters
  localparam ADDITION =     0;
  localparam SUBTRACTION =  1;
  localparam BITWISE_AND =  2;
  localparam BITWISE_OR =   3;
  localparam BITWISE_XOR =  4;
  localparam COMPARISON =   5;
  localparam LEFT_SHIFT =   6;
  localparam RIGHT_SHIFT =  7;
  localparam MULTIPLICATION = 8;
  localparam DIVISION =     9;
  localparam MAX_VALUE = ((2**D_BUS_WIDTH) - 1);
  localparam ZERO_FLAG_INDEX = 0;
  localparam LESS_FLAG_INDEX = 1;
  localparam EQUAL_FLAG_INDEX = 2;
  localparam GREATER_FLAG_INDEX = 3;
  localparam UNDERFLOW_FLAG_INDEX = 4;
  localparam OVERFLOW_FLAG_INDEX = 5;
  
  always @(posedge CLK) begin
    
    if ((ENABLE == 0) || (ARST == 0))
        RESULT = 0;
    
    else begin
        case (OPCODE)
            ADDITION:   RESULT = addition(OPERAND_A, OPERAND_B);
            SUBTRACTION: RESULT = subtraction(OPERAND_A, OPERAND_B);
            BITWISE_AND: RESULT = bitwise_AND(OPERAND_A, OPERAND_B);
            BITWISE_OR: RESULT = bitwise_OR(OPERAND_A, OPERAND_B);
            BITWISE_XOR: RESULT = bitwise_XOR(OPERAND_A, OPERAND_B);
            COMPARISON: RESULT = comparison(OPERAND_A,OPERAND_B);
            LEFT_SHIFT: RESULT = left_shift(OPERAND_A, OPERAND_B);
            RIGHT_SHIFT: RESULT = right_shift(OPERAND_A, OPERAND_B);
            MULTIPLICATION: RESULT = multiplication(OPERAND_A, OPERAND_B);
            DIVISION: RESULT = division(OPERAND_A, OPERAND_B);
            default: RESULT = 0;
            
        endcase
        
    end
  
  end
  
  // Definition of the function addition
  function [(D_BUS_WIDTH - 1): 0] addition (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
    addition = num1 + num2;
    
    if (num2 > (MAX_VALUE - num1))
        REG_FLAGS[OVERFLOW_FLAG_INDEX] = 1;
        
    if (addition == 0)
        REG_FLAGS[ZERO_FLAG_INDEX] = 1;
        
  endfunction
  
  // Definition of the function subtraction
  function [(D_BUS_WIDTH - 1): 0] subtraction (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
    
    if (num2 > num1) begin
        num2 = ~num2;
        num2 = num2 + 1;
        
        subtraction = num1 + num2;
        REG_FLAGS[UNDERFLOW_FLAG_INDEX] = 1;
    end 
    else
        subtraction = num1 - num2;
        
    if (subtraction == 0)
        REG_FLAGS[ZERO_FLAG_INDEX] = 1;
        
  endfunction
  
  // Definition of the function bitwise AND
  function [(D_BUS_WIDTH - 1): 0] bitwise_AND (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
    
    bitwise_AND = num1 & num2;
      
  endfunction
  
  // Definition of the function bitwise OR
  function [(D_BUS_WIDTH - 1): 0] bitwise_OR (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
    
    bitwise_OR = num1 | num2;
      
  endfunction
  
  // Definition of the function bitwise XOR
  function [(D_BUS_WIDTH - 1): 0] bitwise_XOR (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
    
    bitwise_XOR = num1 ^ num2;

  endfunction
  
  // Definition of the function comparison
  function [(D_BUS_WIDTH - 1): 0] comparison(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
    comparison = 0;
    
    if (num1 < num2)
        REG_FLAGS[LESS_FLAG_INDEX] = 1;
    
    else if (num1 == num2) begin
        REG_FLAGS[EQUAL_FLAG_INDEX] = 1;
        comparison = 1;
    end
    
    else
        REG_FLAGS[GREATER_FLAG_INDEX] = 1;

  endfunction
  
  // Definition of the function left shift
  function [(D_BUS_WIDTH - 1): 0] left_shift(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
      
    left_shift = num1 << num2;
      
  endfunction
  
  // Definition of the function right shift
  function [(D_BUS_WIDTH - 1): 0] right_shift(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
    
    right_shift = num1 >> num2;
    
  endfunction
  
  // Definition of the function multiplication
  function [(D_BUS_WIDTH - 1): 0] multiplication(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
    multiplication = 0;
    
    if ((num1 * num2) < MAX_VALUE)
        multiplication = num1 * num2;
    else
        REG_FLAGS[OVERFLOW_FLAG_INDEX] = 1;
        
    if (multiplication == 0)
        REG_FLAGS[ZERO_FLAG_INDEX] = 1;
      
  endfunction
  
  // Definition of the function division
  function [(D_BUS_WIDTH - 1): 0] division(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    REG_FLAGS = 0;
    
    if (num2 != 0)
        division = num1 / num2;
    else begin
        division = 0;
    end
    
    if (division == 0)
        REG_FLAGS[ZERO_FLAG_INDEX] = 1;
      
  endfunction
  
endmodule