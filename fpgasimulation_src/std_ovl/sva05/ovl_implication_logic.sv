// Accellera Standard V2.3 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2008. All rights reserved.

`ifdef OVL_ASSERT_ON

  property ASSERT_IMPLICATION_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  antecedent_expr |-> consequent_expr;
  endproperty

  wire fire_2state;
  reg fire_2state_implication;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_2state_implication = 1'b0;
  end
`endif

  assign fire_2state = fire_2state_implication ?
                       ovl_fire_2state_f(property_type) : 1'b0;

`ifdef OVL_XCHECK_OFF
   wire fire_xcheck = 0; 
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
     wire fire_xcheck = 0; 
  `else

  property ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P;
  @ (posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (!consequent_expr) |-> (!($isunknown(antecedent_expr)));
  endproperty

  property ASSERT_IMPLICATION_XZ_ON_CON_EXP_P;
  @ (posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  antecedent_expr |-> (!($isunknown(consequent_expr)));
  endproperty

  wire fire_xcheck;
  reg fire_xcheck_antecedent, fire_xcheck_consequent;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_xcheck_antecedent = 1'b0;
    fire_xcheck_consequent = 1'b0;
  end
`endif

  assign fire_xcheck = (fire_xcheck_antecedent || fire_xcheck_consequent) ?
                       ovl_fire_xcheck_f(property_type) : 1'b0; 

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        A_ASSERT_IMPLICATION_P: assert property (ASSERT_IMPLICATION_P)
                                fire_2state_implication <= 1'b0;
                                else begin
                                  ovl_error_t(`OVL_FIRE_2STATE,"Antecedent does not have consequent");
                                  fire_2state_implication <= 1'b1;
                                end 
                                   

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P:
        assert property (ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P)
        fire_xcheck_antecedent <= 1'b0;
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"antecedent_expr contains X or Z");
          fire_xcheck_antecedent <= 1'b1;
        end

        A_ASSERT_IMPLICATION_XZ_ON_CON_EXP_P:
        assert property (ASSERT_IMPLICATION_XZ_ON_CON_EXP_P)
        fire_xcheck_consequent <= 1'b0;
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"consequent_expr contains X or Z");
          fire_xcheck_consequent <= 1'b1; 
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_IMPLICATION_P: assume property (ASSERT_IMPLICATION_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P:
        assume property (ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P);

        M_ASSERT_IMPLICATION_XZ_ON_CON_EXP_P:
        assume property (ASSERT_IMPLICATION_XZ_ON_CON_EXP_P);
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_IGNORE : begin : ovl_ignore
        // do nothing
      end

      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase

  endgenerate

`else // OVL_ASSERT_ON

  wire fire_2state = 0;
  wire fire_xcheck = 0;

`endif // OVL_ASSERT_ON

`ifdef OVL_COVER_ON

  wire fire_cover;
  reg fire_cover_antecedent;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_cover_antecedent = 1'b0;
  end
`endif

  assign fire_cover = fire_cover_antecedent ?
                      ovl_fire_cover_f(coverage_level) : 1'b0;

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
     if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      cover_antecedent:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) 
                     && antecedent_expr) ) begin
                       ovl_cover_t("antecedent covered");
                       fire_cover_antecedent <= 1'b1;
                     end

     end
    end

  endgenerate

`else // OVL_COVER_ON

   wire fire_cover = 0;

`endif // OVL_COVER_ON
