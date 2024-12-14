`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: CINVESTAV Guadalajara Unit
// Engineers: 
// Lino Rosauro González Guerra
// Eduardo Rafael Heredia González
// Emmanuel Díaz Marín

// Create Date: 24.11.2024 08:33:53
// Design Name: 
// Module Name: VECTORIAL_ALU
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


module VECTORIAL_ALU #(parameter D_BUS_WIDTH = 4, parameter REG_FLAGS_WIDTH = 6, parameter OPCODE_WIDTH = 4, parameter TOTAL_OF_ALUS = 8)(
    output reg [((REG_FLAGS_WIDTH * TOTAL_OF_ALUS) - 1):0] SIGNALS, // Concatenated reg_flags
    output reg [((D_BUS_WIDTH * TOTAL_OF_ALUS) - 1):0] Z,           // Concatenated results
    input [((D_BUS_WIDTH * TOTAL_OF_ALUS) - 1):0] A,
    input [((D_BUS_WIDTH * TOTAL_OF_ALUS) - 1):0] B,
    input [(OPCODE_WIDTH - 1):0] SEL,                               // Opcode for all ALUs
    input [(TOTAL_OF_ALUS - 1):0]ENABLE,                            // Concatenated enables
    input CLK,                                                      // CLK for all ALUs
    input [(TOTAL_OF_ALUS - 1):0]RST                               // Concatenated async resets 
);  
  
  //________________________________________________________ ALUs generation
  generate
    for (genvar alu_index = 0; alu_index < TOTAL_OF_ALUS; alu_index = alu_index + 1) begin : alu_inst
      ALU #(
        .D_BUS_WIDTH(D_BUS_WIDTH),
        .REG_FLAGS_WIDTH(REG_FLAGS_WIDTH),
        .OPCODE_WIDTH(OPCODE_WIDTH)
      ) alu (
        .REG_FLAGS(SIGNALS[((REG_FLAGS_WIDTH * (alu_index + 1)) - 1): (REG_FLAGS_WIDTH * alu_index)]),
        .RESULT(Z[((D_BUS_WIDTH * (alu_index + 1)) - 1) : (D_BUS_WIDTH * alu_index)]),
        .OPERAND_A(A[((D_BUS_WIDTH * (alu_index + 1)) - 1) : (D_BUS_WIDTH * alu_index)]),
        .OPERAND_B(B[((D_BUS_WIDTH * (alu_index + 1)) - 1) : (D_BUS_WIDTH * alu_index)]),
        .OPCODE(SEL),
        .ENABLE(ENABLE[alu_index]),
        .CLK(CLK),
        .RST(RST[alu_index])
      );
    end
    
  endgenerate 
   
endmodule