// Accellera Standard V2.3 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2008. All rights reserved.

`ifdef OVL_ASSERT_ON

  property ASSERT_RANGE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (((test_expr >= min) && (test_expr <= max)) != 1'b0);
  endproperty

  wire fire_2state;
  reg fire_2state_range;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_2state_range = 1'b0;
  end
`endif

  assign fire_2state = fire_2state_range ?
                       ovl_fire_2state_f(property_type) : 1'b0;

`ifdef OVL_XCHECK_OFF
   wire fire_xcheck = 0;
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
     wire fire_xcheck = 0;
  `else

    property ASSERT_RANGE_XZ_ON_TEST_EXPR_P;
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
        A_ASSERT_RANGE_P:
        assert property (ASSERT_RANGE_P)
        fire_2state_range <= 1'b0;
        else begin
          ovl_error_t(`OVL_FIRE_2STATE,"Test expression evaluates to a value outside the range specified by parameters min and max");
          fire_2state_range <= 1'b1; 
        end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
       A_ASSERT_RANGE_XZ_ON_TEST_EXPR_P:
       assert property (ASSERT_RANGE_XZ_ON_TEST_EXPR_P)
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
        M_ASSERT_RANGE_P: assume property (ASSERT_RANGE_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
         M_ASSERT_RANGE_XZ_ON_TEST_EXPR_P:
         assume property (ASSERT_RANGE_XZ_ON_TEST_EXPR_P);
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

  wire fire_cover;
  reg fire_cover_test_expr_change,
      fire_cover_test_expr_at_min,
      fire_cover_test_expr_at_max;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_cover_test_expr_change = 1'b0;
    fire_cover_test_expr_at_min = 1'b0;
    fire_cover_test_expr_at_max = 1'b0;
  end
`endif

  assign fire_cover = (fire_cover_test_expr_change ||
                       fire_cover_test_expr_at_min ||
                       fire_cover_test_expr_at_max) ?
                      ovl_fire_cover_f(coverage_level) : 1'b0;


generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
     if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

      cover_test_expr_change:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) && 
                     !$stable(test_expr) ) ) begin
                       ovl_cover_t("test_expr_change covered");
                       fire_cover_test_expr_change <= 1'b1;
                     end
     end //sanity coverage

     if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

      cover_test_expr_at_min:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) &&
                     $rose(test_expr == min) ) ) begin
                       ovl_cover_t("test_expr_at_min covered");
                       fire_cover_test_expr_at_min <= 1'b1;
                     end
      cover_test_expr_at_max:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) &&
                     $rose(test_expr == max) ) ) begin
                       ovl_cover_t("test_expr_at_max covered");
                       fire_cover_test_expr_at_max <= 1'b1;
                     end
     end
    end

endgenerate

`else // OVL_COVER_ON

   wire fire_cover = 0;

`endif // OVL_COVER_ON

