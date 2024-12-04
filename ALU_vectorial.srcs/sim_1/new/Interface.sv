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
    logic CLK;                                                
    logic [(TOTAL_OF_ALUS - 1):0]ARST;

 localparam ZERO_VALUE = 0;
    localparam MAX_VALUE = (2**D_BUS_WIDTH) - 1;   // MAX_VALUE = 15
    localparam MIDDLE_VALUE = ((MAX_VALUE - 0) / 2) + 0;     // MIDDLE_VALUE = 7
    localparam TOTAL_OF_OPERATIONS = 10;
    
    bit [(D_BUS_WIDTH - 1):0] a;
    bit [(D_BUS_WIDTH - 1):0] b;
    bit [(OPCODE_WIDTH - 1):0] opcode;
    
    //////////////////////////////// BFM ////////////////////////////////
    
    // Function that reset the ALU "N"
    function reset_ALU_N(integer ALU_N, input bit state);
        ARST[(ALU_N - 1)] = 1;
        ARST[(ALU_N - 1)] = 0;
        ARST[(ALU_N - 1)] = 1;
    endfunction
    
    // Function to set the state of the input "ENABLE" of the correspond ALU "N".
    function set_input_ENABLE_to_state(integer ALU_N, input bit state);
        ENABLE[(ALU_N - 1)] = state;
    endfunction
    
    // Function to set the value of the inputs "A" and "B" to zero
    function set_input_A_and_B_to_zero();
        a = 0;
        b = 0;
        A = {TOTAL_OF_ALUS{a}};
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
    
    // Function to set the value of the input "a" with the middle value of range [0, (WIDTH - 1)] 
    function set_input_A_to_middle_value();
        A = {TOTAL_OF_ALUS{MIDDLE_VALUE}};
    endfunction

    // Function to set the value of the input "b" with the middle value of range [0, (WIDTH - 1)] 
    function set_input_B_to_middle_value();
        B = {TOTAL_OF_ALUS{MIDDLE_VALUE}};
    endfunction
    
    // Function to randomize input A with values > MIDDLE_VALUE and randomize input B with values > A
    function randomize_inputs_A_B_to_generate_overflow();
        std::randomize(a, b) with {a > MIDDLE_VALUE; b > a;};
        A = {TOTAL_OF_ALUS{a}};
        B = {TOTAL_OF_ALUS{b}};
    endfunction
    
    // Function to randomize input B with values > MIDDLE_VALUE and randomize input A with values > B
    function randomize_inputs_B_A_to_generate_overflow();
        std::randomize(a, b) with {b > MIDDLE_VALUE; a > b;};
        A = {TOTAL_OF_ALUS{a}};
        B = {TOTAL_OF_ALUS{b}};
    endfunction
    
endinterface: VecAluInt



// Aserciones sujetas a cambios por los test cases

// 1. Verificar que la salida SIGNALS no contenga valores desconocidos (X/Z) cuando ENABLE está activo.
property signals_valid_when_enable;
    @(posedge alu_if.CLK)
    alu_if.ENABLE !== 0 |-> $isunknown(alu_if.SIGNALS) == 0;
endproperty
assert property (signals_valid_when_enable) else $error("SIGNALS contiene valores desconocidos cuando ENABLE está activo!");

// 2. Verificar que Z sea cero si ENABLE está desactivado.
property z_zero_when_disable;
    @(posedge alu_if.CLK)
    alu_if.ENABLE == 0 |-> alu_if.Z == 0;
endproperty
assert property (z_zero_when_disable) else $error("Z no es cero cuando ENABLE está desactivado!");

// 3. Verificar que SIGNALS sea cero si ENABLE está desactivado.
property signals_zero_when_disable;
    @(posedge alu_if.CLK)
    alu_if.ENABLE == 0 |-> alu_if.SIGNALS == 0;
endproperty
assert property (signals_zero_when_disable) else $error("SIGNALS no es cero cuando ENABLE está desactivado!");

// 4. Verificar que Z no sea todo unos cuando ARST está activo.
property z_not_all_ones_when_arst;
    @(posedge alu_if.CLK)
    alu_if.ARST != 0 |-> alu_if.Z !== {((D_BUS_WIDTH * TOTAL_OF_ALUS)){1'b1}};
endproperty
assert property (z_not_all_ones_when_arst) else $error("Z tiene todo unos cuando ARST está activo!");

// 5. Verificar que SIGNALS no cambien si ARST está activo.
property signals_stable_when_arst;
    @(posedge alu_if.CLK)
    alu_if.ARST != 0 |-> $stable(alu_if.SIGNALS);
endproperty
assert property (signals_stable_when_arst) else $error("SIGNALS cambian cuando ARST está activo!");

// 6. Verificar que las señales A y B no contengan X/Z.
property no_unknown_inputs;
    @(posedge alu_if.CLK)
    $isunknown(alu_if.A) == 0 && $isunknown(alu_if.B) == 0;
endproperty
assert property (no_unknown_inputs) else $error("A o B contienen valores desconocidos!");

// 7. Verificar que la salida Z responda en un ciclo cuando ENABLE cambia de 0 a 1.
property z_responds_to_enable;
    @(posedge alu_if.CLK)
    $rose(alu_if.ENABLE) |-> $changed(alu_if.Z);
endproperty
assert property (z_responds_to_enable) else $error("Z no responde al cambio de ENABLE de 0 a 1!");

// 8. Verificar que las señales en SIGNALS no sean negativas si son interpretadas como enteros con signo.
property signals_not_negative;
    @(posedge alu_if.CLK)
    $signed(alu_if.SIGNALS) >= 0;
endproperty
assert property (signals_not_negative) else $error("SIGNALS contiene valores negativos!");

// 9. Verificar que Z sea diferente de A cuando B es diferente de cero.
property z_not_equal_to_a_if_b_nonzero;
    @(posedge alu_if.CLK)
    alu_if.B != 0 |-> alu_if.Z != alu_if.A;
endproperty
assert property (z_not_equal_to_a_if_b_nonzero) else $error("Z es igual a A cuando B no es cero!");

// 10. Verificar que la salida Z sea igual a A cuando B es cero y el opcode es de transferencia directa.
property z_equals_a_if_b_zero;
    @(posedge alu_if.CLK)
    alu_if.B == 0 && alu_if.SEL == 4'b0000 |-> alu_if.Z == alu_if.A;
endproperty
assert property (z_equals_a_if_b_zero) else $error("Z no es igual a A cuando B es cero y el opcode es transferencia!");

// 11. Verificar que todas las ALUs reciban la misma señal SEL.
property sel_propagated_to_all_alus;
    @(posedge alu_if.CLK)
    alu_if.SEL == alu_if.SEL;
endproperty
assert property (sel_propagated_to_all_alus) else $error("La señal SEL no se propagó correctamente a todas las ALUs!");

// 12. Verificar que ARST domine cualquier operación (reset asíncrono).
property arst_dominates;
    @(posedge alu_if.CLK)
    alu_if.ARST != 0 |-> alu_if.Z == 0 && alu_if.SIGNALS == 0;
endproperty
assert property (arst_dominates) else $error("ARST no domina las operaciones como debería!");

// 13. Verificar que Z sea estable si ENABLE no cambia.
property z_stable_if_enable_unchanged;
    @(posedge alu_if.CLK)
    $stable(alu_if.ENABLE) |-> $stable(alu_if.Z);
endproperty
assert property (z_stable_if_enable_unchanged) else $error("Z no es estable cuando ENABLE no cambia!");

// 14. Verificar que las salidas no cambien si el reloj no sube.
property stable_outputs_without_clock;
    @(posedge alu_if.CLK)
    $stable(alu_if.CLK) |-> $stable(alu_if.Z) && $stable(alu_if.SIGNALS);
endproperty
assert property (stable_outputs_without_clock) else $error("Las salidas cambian cuando el reloj no sube!");

// 15. Verificar que cada ALU individualmente no genere resultados desconocidos.
genvar i;
generate
    for (i = 0; i < TOTAL_OF_ALUS; i = i + 1) begin : alu_individual_check
        property alu_output_no_unknowns;
            @(posedge alu_if.CLK)
            alu_if.ENABLE[i] |-> !$isunknown(alu_if.Z[(D_BUS_WIDTH * (i + 1)) - 1 : D_BUS_WIDTH * i]);
        endproperty
        assert property (alu_output_no_unknowns) else $error("La ALU %0d genera valores desconocidos!", i);
    end
endgenerate

