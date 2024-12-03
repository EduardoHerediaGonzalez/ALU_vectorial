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

interface VecAluInt(parameter D_BUS_WIDTH = 4, parameter REG_FLAGS_WIDTH = 6, parameter OPCODE_WIDTH = 4, parameter TOTAL_OF_ALUS = 8) ();
    logic [((REG_FLAGS_WIDTH * TOTAL_OF_ALUS) - 1):0] SIGNALS;
    logic [((D_BUS_WIDTH * TOTAL_OF_ALUS) - 1):0] Z;          
    logic [((D_BUS_WIDTH * TOTAL_OF_ALUS) - 1):0] A;
    logic [((D_BUS_WIDTH * TOTAL_OF_ALUS) - 1):0] B;
    logic [(OPCODE_WIDTH - 1):0] SEL;                               
    logic [(TOTAL_OF_ALUS - 1):0]ENABLE;                         
    logic CLK;                                                
    logic [(TOTAL_OF_ALUS - 1):0]ARST;

    //TODO: Add BFM functions

endinterface VecAluInt
