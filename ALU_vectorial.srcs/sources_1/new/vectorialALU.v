`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.11.2024 08:33:53
// Design Name: 
// Module Name: vectorialALU
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


module vectorialALU #(parameter D_BUS_WIDTH=8, NUM_ALUS = 10)(
  input [(D_BUS_WIDTH * NUM_ALUS)-1:0] operand_a,
  input [(D_BUS_WIDTH * NUM_ALUS)-1:0] operand_b,
  input [3:0] opcode,                                       // Opcode for all ALUs
  output [NUM_ALUS-1:0] equal_flag,                         // Concatenated equal flags
  output [NUM_ALUS-1:0] less_flag,                          // Concatenated less flags
  output [NUM_ALUS-1:0] greater_flag,                       // Concatenated greater flags
  output [NUM_ALUS-1:0] overflow_flag,                      // Concatenated overflow flags
  output [(D_BUS_WIDTH * NUM_ALUS)-1:0] result              // Concatenated results
    );

  //________________________________________________________ Internal signals to connect individual ALUs
  wire [(D_BUS_WIDTH * NUM_ALUS)-1:0] result_concatenated;
  
  
  //________________________________________________________ ALUs generation
  generate
    for ( genvar i = 0; i < NUM_ALUS; i = i + 1) begin : alu_inst
      ALU #(
        .D_BUS_WIDTH(D_BUS_WIDTH) 
      ) alu (
        .equal_flag(equal_flag[i]),
        .less_flag(less_flag[i]),
        .greater_flag(greater_flag[i]),
        .overflow_flag(overflow_flag[i]),
        .result(result_concatenated[(D_BUS_WIDTH*(i+1)-1) : (D_BUS_WIDTH*i)]),
        .operand_A(operand_a[(D_BUS_WIDTH*(i+1)-1) : (D_BUS_WIDTH*i)]),
        .operand_B(operand_b[(D_BUS_WIDTH*(i+1)-1) : (D_BUS_WIDTH*i)]),
        .opcode(opcode)
      );
    end
  endgenerate
  
  assign result = result_concatenated;                      // Concatenate individual results to form the final output
  
endmodule