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



module vectorialALU_TB #(parameter D_BUS_WIDTH=4, REG_FLAGS_WIDTH=6, OPCODE_WIDTH=4, TOTAL_OF_ALUS=8);
    bit clk;
    
    VecAluInt #(D_BUS_WIDTH, REG_FLAGS_WIDTH, OPCODE_WIDTH, TOTAL_OF_ALUS) alu_if ();  //___________ Interface instantiation
    
    VECTORIAL_ALU #(D_BUS_WIDTH, REG_FLAGS_WIDTH, OPCODE_WIDTH, TOTAL_OF_ALUS) DUT (  //___________ DUT instantiation                                      
        .SIGNALS(alu_if.SIGNALS),
        .Z(alu_if.Z),
        .A(alu_if.A),
        .B(alu_if.B),
        .SEL(alu_if.SEL),                               
        .ENABLE(alu_if.ENABLE),                         
        .CLK(clk),                                                
        .ARST(alu_if.ARST)
    );                               

    localparam v = ((TOTAL_OF_ALUS * D_BUS_WIDTH) - 1);
    localparam ZERO_FLAG_INDEX = 0;
    localparam LESS_FLAG_INDEX = 1;
    localparam EQUAL_FLAG_INDEX = 2;
    localparam GREATER_FLAG_INDEX = 3;
    localparam UNDERFLOW_FLAG_INDEX = 4;
    localparam OVERFLOW_FLAG_INDEX = 5;
    bit [(REG_FLAGS_WIDTH - 1):0] signals_reg;
//______________________________________________________________ Assertion definitions 
    
    property x;
        @(posedge clk)
        ((alu_if.SEL == 0) && (alu_if.A == alu_if.set_input_A_to_zero()) && (alu_if.B == alu_if.set_input_B_to_zero())) |-> alu_if.Z == 15;
    endproperty
    assert property (x) else $error("Z is not zero when both inputs are zero");
    
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
        selc: coverpoint alu_if.SEL {
            ignore_bins ib = {[10:15]};
        }
        
        aOPaddition: coverpoint alu_if.A iff(alu_if.SEL == 0);
        bOPaddition: coverpoint alu_if.B iff(alu_if.SEL == 0);
        zOPaddition: coverpoint alu_if.Z iff(alu_if.SEL == 0);
        
        aOPsubtraction: coverpoint alu_if.A iff(alu_if.SEL == 1);
        bOPsubtraction: coverpoint alu_if.B iff(alu_if.SEL == 1);
        zOPsubtraction: coverpoint alu_if.Z iff(alu_if.SEL == 1);
        
        aOPmultilpication: coverpoint alu_if.A iff(alu_if.SEL == 8);
        bOPmultilpication: coverpoint alu_if.B iff(alu_if.SEL == 8);
        zOPmultilpication: coverpoint alu_if.Z iff(alu_if.SEL == 8);
        
        aOPdivision: coverpoint alu_if.A iff(alu_if.SEL == 9);
        bOPdivision: coverpoint alu_if.B iff(alu_if.SEL == 9);
        zOPdivision: coverpoint alu_if.Z iff(alu_if.SEL == 9);
        
        aOPleftshift: coverpoint alu_if.A iff(alu_if.SEL == 6);
        bOPleftshift: coverpoint alu_if.B iff(alu_if.SEL == 6);
        zOPleftshift: coverpoint alu_if.Z iff(alu_if.SEL == 6);
        
        aOPrightshift: coverpoint alu_if.A iff(alu_if.SEL == 7);
        bOPrightshift: coverpoint alu_if.B iff(alu_if.SEL == 7);
        zOPrightshift: coverpoint alu_if.Z iff(alu_if.SEL == 7);
        
        aOPbwAND: coverpoint alu_if.A iff(alu_if.SEL == 2);
        bOPbwAND: coverpoint alu_if.B iff(alu_if.SEL == 2);
        zOPbwAND: coverpoint alu_if.Z iff(alu_if.SEL == 2);
        
        aOPbwOR: coverpoint alu_if.A iff(alu_if.SEL == 3);
        bOPbwOR: coverpoint alu_if.B iff(alu_if.SEL == 3);
        zOPbwOR: coverpoint alu_if.Z iff(alu_if.SEL == 3);
        
        aOPbwXOR: coverpoint alu_if.A iff(alu_if.SEL == 4);
        bOPbwXOR: coverpoint alu_if.B iff(alu_if.SEL == 4);
        zOPbwXOR: coverpoint alu_if.Z iff(alu_if.SEL == 4);
        
        aOPcomparison: coverpoint alu_if.A iff(alu_if.SEL == 5);
        bOPcomparison: coverpoint alu_if.B iff(alu_if.SEL == 5);
        zOPcomparison: coverpoint alu_if.Z iff(alu_if.SEL == 5);
        
        aSelect: cross alu_if.A, selc;
        bSelect: cross alu_if.B, selc;
        zSelect: cross alu_if.Z, selc;
           
    endgroup
    
    
 
    cg_vectorial_ALU vALUCoverGroupInstance = new();


//______________________________________________________________ Tests definitions
  `define ADDITION_TESTS
//  `define SUBTRACTION_TESTS
//  `define MULTIPLICATION_TESTS
//  `define DIVISION_TESTS
//  `define COMPARISON_TESTS
//  `define BITWISE_AND_TESTS
//  `define BITWISE_OR_TESTS
//  `define BITWISE_XOR_TESTS

    event test_1_event;
    event test_2_event;
    event test_3_event;
    event test_4_event;
    event test_5_event;
    event test_6_event;
    event test_7_event;
    event tests_finished_event;


//______________________________________________________________ Processes definitions

    always #1 clk = !clk;
    
    ///////////////////////////////////////// SUBTRACTION TEST /////////////////////////////////////////    
    `ifdef ADDITION_TESTS
    initial begin
        alu_if.set_operation_to("ADDITION");
        alu_if.set_all_ALUS_ENABLE_to_state(1);
        ->test_1_event;
    end
    
    always @(test_1_event) begin
        alu_if.set_input_A_and_B_to_zero();
        @(posedge clk);
        ->test_2_event;
    end
    
    always @(test_2_event) begin 
        alu_if.set_input_A_to_zero();
        alu_if.set_input_B_to_max_value();
        @(posedge clk);
        ->test_3_event;
    end
    
    always @(test_3_event) begin 
        alu_if.set_input_A_to_max_value();
        alu_if.set_input_B_to_zero();
        @(posedge clk);
        ->test_4_event;
    end
    
    always @(test_4_event) begin 
        alu_if.set_input_A_and_B_to_max_value();
        @(posedge clk);
        ->test_5_event;
    end
    
    always @(test_5_event) begin 
        repeat(100) begin
            alu_if.randomize_inputs_A_and_B_to_generate_overflow();
            @(posedge clk);
        end
        ->test_6_event;
    end
    
    always @(test_6_event) begin 
        repeat(100) begin
            alu_if.randomize_inputs_B_and_A_to_generate_overflow();
            @(posedge clk);
        end
        ->test_7_event;
    end
    
    always @(test_7_event) begin 
        alu_if.set_all_ALUS_ENABLE_to_state(0);
        repeat(10) begin
            alu_if.randomize_input_A();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->tests_finished_event;
    end
    
    initial begin
        wait(tests_finished_event.triggered);
        $finish;
    end
    `endif
    
    ///////////////////////////////////////// SUBTRACTION TEST ///////////////////////////////////////// 
    `ifdef SUBTRACTION_TESTS
    initial begin
        alu_if.set_operation_to("SUBTRACTION");
        alu_if.set_all_ALUS_ENABLE_to_state(1);
        ->test_1_event;
    end
    
    always @(test_1_event) begin
        alu_if.set_input_A_and_B_to_zero();
        @(posedge clk);
        ->test_2_event;
    end
    
    always @(test_2_event) begin 
        alu_if.set_input_A_to_zero();
        alu_if.set_input_B_to_max_value();
        @(posedge clk);
        ->test_3_event;
    end
    
    always @(test_3_event) begin 
        alu_if.set_input_A_to_max_value();
        alu_if.set_input_B_to_zero();
        @(posedge clk);
        ->test_4_event;
    end
    
    always @(test_4_event) begin 
        alu_if.set_input_A_and_B_to_max_value();
        @(posedge clk);
        ->test_5_event;
    end
    
    always @(test_5_event) begin 
        repeat(100) begin
            alu_if.randomize_inputs_A_and_B_to_generate_underflow();
            @(posedge clk);
        end
        ->test_6_event;
    end
    
    always @(test_6_event) begin 
        alu_if.set_all_ALUS_ENABLE_to_state(0);
        repeat(10) begin
            alu_if.randomize_input_A();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->tests_finished_event;
    end
    
    initial begin
        wait(tests_finished_event.triggered);
        $finish;
    end
    `endif

    ///////////////////////////////////////// MULTIPLICATION TEST ///////////////////////////////////////// 
    `ifdef MULTIPLCATION_TESTS
    initial begin
        alu_if.set_operation_to("MULTIPLICATION");
        alu_if.set_all_ALUS_ENABLE_to_state(1);
        ->test_1_event;
    end
    
    always @(test_1_event) begin
        alu_if.set_input_A_and_B_to_zero();
        @(posedge clk);
        ->test_2_event;
    end
    
    always @(test_2_event) begin 
        alu_if.set_input_A_to_zero();
        alu_if.set_input_B_to_max_value();
        @(posedge clk);
        ->test_3_event;
    end
    
    always @(test_3_event) begin 
        alu_if.set_input_A_to_max_value();
        alu_if.set_input_B_to_zero();
        @(posedge clk);
        ->test_4_event;
    end
    
    always @(test_4_event) begin 
        alu_if.set_input_A_and_B_to_max_value();
        @(posedge clk);
        ->test_5_event;
    end
    
    always @(test_5_event) begin 
        repeat(100) begin
            alu_if.randomize_inputs_A_and_B_to_generate_overflow();
            @(posedge clk);
        end
        ->test_6_event;
    end
    
    always @(test_6_event) begin 
        repeat(100) begin
            alu_if.randomize_inputs_B_and_A_to_generate_overflow();
            @(posedge clk);
        end
        ->test_7_event;
    end
    
    always @(test_7_event) begin 
        alu_if.set_all_ALUS_ENABLE_to_state(0);
        repeat(10) begin
            alu_if.randomize_input_A();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->tests_finished_event;
    end
    
    initial begin
        wait(tests_finished_event.triggered);
        $finish;
    end
    `endif
    
    ///////////////////////////////////////// DIVISION TEST ///////////////////////////////////////// 
    `ifdef DIVISION_TESTS
    initial begin
        alu_if.set_operation_to("DIVISION");
        alu_if.set_all_ALUS_ENABLE_to_state(1);
        ->test_1_event;
    end
    
    always @(test_1_event) begin
        repeat(100) begin
            alu_if.set_input_A_to_zero();
            alu_if.randomize_input_B_distinct_to_zero();
            @(posedge clk);
        end
        ->test_2_event;
    end
    
    always @(test_2_event) begin
        repeat(100) begin 
            alu_if.randomize_input_A_distinct_to_zero();
            alu_if.set_input_B_to_zero();
            @(posedge clk);
        end
        ->test_3_event;
    end
    
    always @(test_3_event) begin
        repeat(100) begin 
            alu_if.randomize_input_A_distinct_to_zero();
            alu_if.randomize_input_B_distinct_to_zero();
            @(posedge clk);
        end
        ->test_4_event;
    end
    
    always @(test_4_event) begin 
        alu_if.set_input_A_and_B_to_max_value();
        @(posedge clk);
        ->test_5_event;
    end
    
    always @(test_5_event) begin 
        alu_if.set_all_ALUS_ENABLE_to_state(0);
        repeat(10) begin
            alu_if.randomize_input_A_distinct_to_zero();
            alu_if.randomize_input_B_distinct_to_zero();
            @(posedge clk);
        end
        ->tests_finished_event;
    end
    
    initial begin
        wait(tests_finished_event.triggered);
        $finish;
    end
    `endif
    
    ///////////////////////////////////////// COMPARISON TEST ///////////////////////////////////////// 
    `ifdef COMPARISON_TESTS
    initial begin
        alu_if.set_operation_to("COMPARISON");
        alu_if.set_all_ALUS_ENABLE_to_state(1);
        ->test_1_event;
    end
    
    always @(test_1_event) begin
        alu_if.set_input_A_to_zero();
        alu_if.set_input_B_to_zero();
        @(posedge clk);
        ->test_2_event;
    end
    
    always @(test_2_event) begin
        alu_if.set_input_A_to_max_value();
        alu_if.set_input_B_to_max_value();
        @(posedge clk);
        ->test_3_event;
    end
    
    always @(test_3_event) begin
        repeat(100) begin 
            alu_if.randomize_input_A();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->test_4_event;
    end
    
    always @(test_4_event) begin 
        alu_if.set_all_ALUS_ENABLE_to_state(0);
        repeat(10) begin
            alu_if.randomize_input_A();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->tests_finished_event;
    end
    
    initial begin
        wait(tests_finished_event.triggered);
        $finish;
    end
    `endif
    
    ///////////////////////////////////////// BITWISE_AND TEST ///////////////////////////////////////// 
    `ifdef BITWISE_AND_TESTS
    initial begin
        alu_if.set_operation_to("BITWISE_AND");
        alu_if.set_all_ALUS_ENABLE_to_state(1);
        ->test_1_event;
    end
    
    always @(test_1_event) begin
        alu_if.set_input_A_to_zero();
        alu_if.set_input_B_to_zero();
        @(posedge clk);
        ->test_2_event;
    end
    
    always @(test_2_event) begin
        alu_if.set_input_A_to_max_value();
        alu_if.set_input_B_to_max_value();
        @(posedge clk);
        ->test_3_event;
    end
    
    always @(test_3_event) begin
        repeat(100) begin 
            alu_if.set_input_A_to_zero();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->test_4_event;
    end
    
    always @(test_4_event) begin
        repeat(100) begin 
            alu_if.randomize_input_A();
            alu_if.set_input_B_to_zero();
            @(posedge clk);
        end
        ->test_5_event;
    end
    
    always @(test_5_event) begin 
        alu_if.set_all_ALUS_ENABLE_to_state(0);
        repeat(10) begin
            alu_if.randomize_input_A();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->tests_finished_event;
    end
    
    initial begin
        wait(tests_finished_event.triggered);
        $finish;
    end
    `endif
    
    ///////////////////////////////////////// BITWISE_OR TEST ///////////////////////////////////////// 
    `ifdef BITWISE_OR_TESTS
    initial begin
        alu_if.set_operation_to("BITWISE_OR");
        alu_if.set_all_ALUS_ENABLE_to_state(1);
        ->test_1_event;
    end
    
    always @(test_1_event) begin
        alu_if.set_input_A_to_zero();
        alu_if.set_input_B_to_zero();
        @(posedge clk);
        ->test_2_event;
    end
    
    always @(test_2_event) begin
        alu_if.set_input_A_to_max_value();
        alu_if.set_input_B_to_max_value();
        @(posedge clk);
        ->test_3_event;
    end
    
    always @(test_3_event) begin
        repeat(100) begin 
            alu_if.set_input_A_to_zero();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->test_4_event;
    end
    
    always @(test_4_event) begin
        repeat(100) begin 
            alu_if.randomize_input_A();
            alu_if.set_input_B_to_zero();
            @(posedge clk);
        end
        ->test_5_event;
    end
    
    always @(test_5_event) begin 
        alu_if.set_all_ALUS_ENABLE_to_state(0);
        repeat(10) begin
            alu_if.randomize_input_A();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->tests_finished_event;
    end
    
    initial begin
        wait(tests_finished_event.triggered);
        $finish;
    end
    `endif
    
    ///////////////////////////////////////// BITWISE_XOR TEST ///////////////////////////////////////// 
    `ifdef BITWISE_XOR_TESTS
    initial begin
        alu_if.set_operation_to("BITWISE_XOR");
        alu_if.set_all_ALUS_ENABLE_to_state(1);
        ->test_1_event;
    end
    
    always @(test_1_event) begin
        alu_if.set_input_A_to_zero();
        alu_if.set_input_B_to_zero();
        @(posedge clk);
        ->test_2_event;
    end
    
    always @(test_2_event) begin
        alu_if.set_input_A_to_max_value();
        alu_if.set_input_B_to_max_value();
        @(posedge clk);
        ->test_3_event;
    end
    
    always @(test_3_event) begin
        repeat(100) begin 
            alu_if.set_input_A_to_zero();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->test_4_event;
    end
    
    always @(test_4_event) begin
        repeat(100) begin 
            alu_if.randomize_input_A();
            alu_if.set_input_B_to_zero();
            @(posedge clk);
        end
        ->test_5_event;
    end
    
    always @(test_5_event) begin 
        alu_if.set_all_ALUS_ENABLE_to_state(0);
        repeat(10) begin
            alu_if.randomize_input_A();
            alu_if.randomize_input_B();
            @(posedge clk);
        end
        ->tests_finished_event;
    end
    
    initial begin
        wait(tests_finished_event.triggered);
        $finish;
    end
    `endif
    
endmodule



