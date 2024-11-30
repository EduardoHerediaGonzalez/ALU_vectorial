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


module ALU #(parameter D_BUS_WIDTH = 8)(
  output equal_flag,
  output less_flag,
  output greater_flag,
  output reg overflow_flag,
  output [(D_BUS_WIDTH - 1): 0] result,
  input [(D_BUS_WIDTH - 1): 0] operand_A,
  input [(D_BUS_WIDTH - 1): 0] operand_B,
  input [3:0] opcode
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
  
  //Continuous assigments
  assign result =   (opcode == ADDITION)? addition(operand_A, operand_B) :
    				(opcode == SUBTRACTION) ? subtraction(operand_A, operand_B):
                    (opcode == BITWISE_AND) ? bitwise_AND(operand_A, operand_B): 
                    (opcode == BITWISE_OR) ? bitwise_OR(operand_A, operand_B): 
                    (opcode == BITWISE_XOR) ? bitwise_XOR(operand_A, operand_B): 
                    (opcode == COMPARISON) ? comparison(operand_A,operand_B):
                    (opcode == LEFT_SHIFT) ? left_shift(operand_A, operand_B): 
                    (opcode == RIGHT_SHIFT) ? right_shift(operand_A, operand_B): 
                    (opcode == MULTIPLICATION) ? multiplication(operand_A, operand_B): 
                    (opcode == DIVISION) ? division(operand_A, operand_B): 'b0;
  
  assign flag_equal = (operand_A == operand_B) ? 1'b1: 1'b0;
  assign flag_less =  (operand_A < operand_B) ? 1'b1: 1'b0;
  assign flag_greater = (operand_A > operand_B) ? 1'b1: 1'b0;
  
  //Definition of the function addition
  function [(D_BUS_WIDTH - 1): 0] addition (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      if (num2 <= (MAX_VALUE - num1)) begin
       addition = (num1 + num2);
       end else begin
       addition = 'b0;
       overflow_flag = 1'b1;
       end
    end
  endfunction
  
  //Definition of the function subtraction
  function [(D_BUS_WIDTH - 1): 0] subtraction (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      if (num2 <= num1) begin
        subtraction = num1 - num2;
      end else begin
        subtraction = 'b0;
        overflow_flag = 1'b1;
      end
    end
  endfunction
  
  //Definition of the function bitwise AND
  function [(D_BUS_WIDTH - 1): 0] bitwise_AND (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      bitwise_AND = (num1 & num2);
    end
  endfunction
  
  //Definition of the function bitwise OR
  function [(D_BUS_WIDTH - 1): 0] bitwise_OR (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      bitwise_OR = (num1 | num2);
    end
  endfunction
  
  //Definition of the function bitwise XOR
  function [(D_BUS_WIDTH - 1): 0] bitwise_XOR (input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      bitwise_XOR = num1 ^ num2;
    end
  endfunction
  
  //Definition of the function comparison
  function [(D_BUS_WIDTH - 1): 0] comparison(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      comparison = (num1 == num2);
    end
  endfunction
  
  //Definition of the function left shift
  function [(D_BUS_WIDTH - 1): 0] left_shift(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      left_shift = (num1 << num2);
    end
  endfunction
  
  //Definition of the function right shift
  function [(D_BUS_WIDTH - 1): 0] right_shift(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      right_shift = (num1 >> num2);
    end
  endfunction
  
  //Definition of the function multiplication
  function [(D_BUS_WIDTH - 1): 0] multiplication(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      if ((num1 * num2) < MAX_VALUE) begin
        multiplication = num1 * num2;
      end else begin
        multiplication = 'b0;
        overflow_flag = 1'b1;
      end
    end
  endfunction
  
  //Definition of the function division
  function [(D_BUS_WIDTH - 1): 0] division(input [(D_BUS_WIDTH - 1): 0] num1, num2);
    begin
      if (num2 != 0) begin
        division = num1 / num2;
      end else begin
        division = 'b0;
        overflow_flag = 1'b1;
      end
    end
  endfunction
  
endmodule