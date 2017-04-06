// Accellera Standard V2.3 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2008. All rights reserved.

`ifdef OVL_ASSERT_ON

  property ASSERT_ALWAYS_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)

`ifdef OVL_XCHECK_OFF
    !($isunknown(test_expr)) |->
`else
    //Do not check for unknown by default to improve performance
`endif
    test_expr;
  endproperty

  wire fire_2state;
  reg fire_2state_always;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_2state_always = 1'b0;
  end
`endif

  assign fire_2state = fire_2state_always ?
                       ovl_fire_2state_f(property_type) : 1'b0;


`ifdef OVL_XCHECK_OFF
   wire fire_xcheck = 0;
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
     wire fire_xcheck = 0;
  `else

  property ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (!($isunknown(test_expr)));
  endproperty

  wire fire_xcheck;
  reg fire_xcheck_test_expr;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_xcheck_test_expr = 1'b0;
  end
`endif

  assign fire_xcheck = fire_xcheck_test_expr ?
                       ovl_fire_xcheck_f(property_type) : 1'b0;

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        A_ASSERT_ALWAYS_P:
        assert property (ASSERT_ALWAYS_P)
        fire_2state_always <= 1'b0;
        else begin
          ovl_error_t(`OVL_FIRE_2STATE,"Test expression is FALSE");
          fire_2state_always <= 1'b1;
        end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P:
        assert property (ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P)
        fire_xcheck_test_expr <= 1'b0; 
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
          fire_xcheck_test_expr <= 1'b1;
        end
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_ALWAYS_P: assume property (ASSERT_ALWAYS_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P:
        assume property (ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P);
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_IGNORE : begin : ovl_ignore
        // do nothing;
      end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase

  endgenerate

`else // OVL_ASSERT_ON

  wire fire_2state = 0;
  wire fire_xcheck = 0;

`endif // OVL_ASSERT_ON

`ifdef OVL_COVER_ON

   wire fire_cover = 0;
   // No coverpoint is specified for this component

`else // OVL_COVER_ON

   wire fire_cover = 0;

`endif // OVL_COVER_ON

