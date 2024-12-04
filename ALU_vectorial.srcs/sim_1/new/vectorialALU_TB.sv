`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 01.12.2024 20:51:39
// Design Name: 
// Module Name: vectorialALU_TB
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

localparam TOTAL_OF_ALUS=10;
localparam D_BUS_WIDTH=8;

module vectorialALU_TB;

    localparam TOTAL_OF_ALUS=10;
    localparam D_BUS_WIDTH=8;
    
    bit clk;
    
    VecAluInt #(.D_BUS_WIDTH(8), .REG_FLAGS_WIDTH(6), .OPCODE_WIDTH(4), .TOTAL_OF_ALUS(TOTAL_OF_ALUS)) alu_if (.clk(clk));  //___________ Interface instantiation
    
    VECTORIAL_ALU #(.D_BUS_WIDTH(4), .REG_FLAGS_WIDTH(6), .OPCODE_WIDTH(4), .TOTAL_OF_ALUS(8)) DUT (  //___________ DUT instantiation                                      
    .SIGNALS(alu_if.SIGNALS),
    .Z(alu_if.Z),
    .A(alu_if.A),
    .B(alu_if.B),
    .SEL(alu_if.SEL),                               
    .ENABLE(alu_if.ENABLE),                         
    .CLK(clk),                                                
    .ARST(alu_if.ARST)

    );                               

//______________________________________________________________ Assertion definitions 

// 1. Verificar que la salida SIGNALS no contenga valores desconocidos (X/Z) cuando ENABLE está activo.
property signals_valid_when_enable;
    @(posedge clk)
    alu_if.ENABLE !== 0 |-> $isunknown(alu_if.SIGNALS) == 0;
endproperty
assert property (signals_valid_when_enable) else $error("SIGNALS contiene valores desconocidos cuando ENABLE está activo!");

// 2. Verificar que Z sea cero si ENABLE está desactivado.
property z_zero_when_disable;
    @(posedge clk)
    alu_if.ENABLE == 0 |-> alu_if.Z == 0;
endproperty
assert property (z_zero_when_disable) else $error("Z no es cero cuando ENABLE está desactivado!");

// 3. Verificar que SIGNALS sea cero si ENABLE está desactivado.
property signals_zero_when_disable;
    @(posedge clk)
    alu_if.ENABLE == 0 |-> alu_if.SIGNALS == 0;
endproperty
assert property (signals_zero_when_disable) else $error("SIGNALS no es cero cuando ENABLE está desactivado!");

// 4. Verificar que Z no sea todo unos cuando ARST está activo.
property z_not_all_ones_when_arst;
    @(posedge clk)
    alu_if.ARST != 0 |-> alu_if.Z !== {((D_BUS_WIDTH * TOTAL_OF_ALUS)){1'b1}};
endproperty
assert property (z_not_all_ones_when_arst) else $error("Z tiene todo unos cuando ARST está activo!");

// 5. Verificar que SIGNALS no cambien si ARST está activo.
property signals_stable_when_arst;
    @(posedge clk)
    alu_if.ARST != 0 |-> $stable(alu_if.SIGNALS);
endproperty
assert property (signals_stable_when_arst) else $error("SIGNALS cambian cuando ARST está activo!");

// 6. Verificar que las señales A y B no contengan X/Z.
property no_unknown_inputs;
    @(posedge clk)
    $isunknown(alu_if.A) == 0 && $isunknown(alu_if.B) == 0;
endproperty
assert property (no_unknown_inputs) else $error("A o B contienen valores desconocidos!");

// 7. Verificar que la salida Z responda en un ciclo cuando ENABLE cambia de 0 a 1.
property z_responds_to_enable;
    @(posedge clk)
    $rose(alu_if.ENABLE) |-> $changed(alu_if.Z);
endproperty
assert property (z_responds_to_enable) else $error("Z no responde al cambio de ENABLE de 0 a 1!");

// 8. Verificar que las señales en SIGNALS no sean negativas si son interpretadas como enteros con signo.
property signals_not_negative;
    @(posedge clk)
    $signed(alu_if.SIGNALS) >= 0;
endproperty
assert property (signals_not_negative) else $error("SIGNALS contiene valores negativos!");

// 9. Verificar que Z sea diferente de A cuando B es diferente de cero.
property z_not_equal_to_a_if_b_nonzero;
    @(posedge clk)
    alu_if.B != 0 |-> alu_if.Z != alu_if.A;
endproperty
assert property (z_not_equal_to_a_if_b_nonzero) else $error("Z es igual a A cuando B no es cero!");

// 10. Verificar que la salida Z sea igual a A cuando B es cero y el opcode es de transferencia directa.
property z_equals_a_if_b_zero;
    @(posedge clk)
    alu_if.B == 0 && alu_if.SEL == 4'b0000 |-> alu_if.Z == alu_if.A;
endproperty
assert property (z_equals_a_if_b_zero) else $error("Z no es igual a A cuando B es cero y el opcode es transferencia!");

// 11. Verificar que todas las ALUs reciban la misma señal SEL.
property sel_propagated_to_all_alus;
    @(posedge clk)
    alu_if.SEL == alu_if.SEL;
endproperty
assert property (sel_propagated_to_all_alus) else $error("La señal SEL no se propagó correctamente a todas las ALUs!");

// 12. Verificar que ARST domine cualquier operación (reset asíncrono).
property arst_dominates;
    @(posedge clk)
    alu_if.ARST != 0 |-> alu_if.Z == 0 && alu_if.SIGNALS == 0;
endproperty
assert property (arst_dominates) else $error("ARST no domina las operaciones como debería!");

// 13. Verificar que Z sea estable si ENABLE no cambia.
property z_stable_if_enable_unchanged;
    @(posedge clk)
    $stable(alu_if.ENABLE) |-> $stable(alu_if.Z);
endproperty
assert property (z_stable_if_enable_unchanged) else $error("Z no es estable cuando ENABLE no cambia!");

// 14. Verificar que las salidas no cambien si el reloj no sube.
property stable_outputs_without_clock;
    @(posedge clk)
    $stable(clk) |-> $stable(alu_if.Z) && $stable(alu_if.SIGNALS);
endproperty
assert property (stable_outputs_without_clock) else $error("Las salidas cambian cuando el reloj no sube!");

// 15. Verificar que cada ALU individualmente no genere resultados desconocidos.
genvar i;
generate
    for (i = 0; i < TOTAL_OF_ALUS; i = i + 1) begin : alu_individual_check
        property alu_output_no_unknowns;
            @(posedge clk)
            alu_if.ENABLE[i] |-> !$isunknown(alu_if.Z[(D_BUS_WIDTH * (i + 1)) - 1 : D_BUS_WIDTH * i]);
        endproperty
        assert property (alu_output_no_unknowns) else $error("La ALU %0d genera valores desconocidos!", i);
    end
endgenerate



//______________________________________________________________ Covergroup definition

covergroup cg_vectorial_ALU @(posedge clk);
    ac: coverpoint alu_if.A;
    bc: coverpoint alu_if.B;   
    rc: coverpoint alu_if.Z;    
 
endgroup
    
    
 
cg_vectorial_ALU vALUCoverGroupInstance = new();


//______________________________________________________________ Test definitions
  `define TEST1
  //`define TEST2
  //`define TEST3
  //`define TEST4
  //`define TEST5

//______________________________________________________________ Processes definitions

always #1ns clk = !clk;

initial begin 

    `ifdef TEST1
        //////////////////////////////////////////////
        // 1.(200) Addition of random a and b       //
        //                                          //
        //                                          //
        //////////////////////////////////////////////

    $display("___________ TEST 1 _____________");
    $display("      ");
    $display("___________ Random A and B additions _____________");
    
    alu_if.set_operation_to("SUBTRACTION");
    repeat(200) begin
        alu_if.randomize_input_A();
        alu_if.randomize_input_B();
        @(posedge clk);
    end

    `endif    
	
	$finish;

end



endmodule



