// Accellera Standard V2.3 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2008. All rights reserved.


`ifdef OVL_ASSERT_ON

  reg    error_mutex, error_xz_test_expr;
  wire   error_event, error_event_xz;

// Initializing all the error_* signals (except error_event)

`ifdef OVL_SYNTHESIS
`else
  initial begin
    error_mutex        = 1'b0;
    error_xz_test_expr = 1'b0;
  end
`endif

  always @(posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b1) begin
      error_mutex        <= 1'b0;
      error_xz_test_expr <= 1'b0;
    end
  end

  assign error_event    = error_mutex;
  assign error_event_xz = error_xz_test_expr;

`endif // OVL_ASSERT_ON

`ifdef OVL_REVISIT // Tied low in V2.3 (in top-level file)
  `ifdef OVL_ASSERT_ON
    assign fire[0] = error_event;
    assign fire[1] = error_event_xz;
  `else
    assign fire[0] = 1'b0;
    assign fire[1] = 1'b0;
  `endif // OVL_ASSERT_ON

  `ifdef OVL_COVER_ON
    assign fire[2] = 1'b0;
  `else
    assign fire[2] = 1'b0;
  `endif // OVL_COVER_ON
`endif // OVL_REVISIT

`ifdef OVL_SHARED_CODE

  wire [width-1 : 0] bit_vector;

  assign bit_vector = (invert_mode == 0) ? test_expr : ~test_expr;

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property OVL_MUTEX_P;
  @(posedge clk)
  disable iff(`OVL_RESET_SIGNAL != 1'b1)
  (!($countones(bit_vector) > 1));
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_MUTEX_XZ_ON_TEST_EXPR_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(test_expr)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

          A_OVL_MUTEX_P:
          assert property (OVL_MUTEX_P)
            error_mutex <= 1'b0;
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"Expression's bits are not mutually exclusive");
            error_mutex <= 1'b1;
          end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_MUTEX_XZ_ON_TEST_EXPR_P:
        assert property (OVL_MUTEX_XZ_ON_TEST_EXPR_P)
          error_xz_test_expr <= 1'b0;
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
          error_xz_test_expr <= 1'b1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

          M_OVL_MUTEX_P:
          assume property (OVL_MUTEX_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_MUTEX_XZ_ON_TEST_EXPR_P:
        assume property (OVL_MUTEX_XZ_ON_TEST_EXPR_P);

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_IGNORE : begin : ovl_ignore
        // do nothing;
      end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase
  endgenerate

`endif // OVL_ASSERT_ON


`ifdef OVL_COVER_ON

  genvar g;

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

        cover_values_checked :
          cover property(
            @(posedge clk)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(bit_vector))
             ovl_cover_t("Test expression changed value");

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

        for (g = 0; g < width; g=g+1) begin : mutex_bitmap
          cover_mutex_bitmap:
            cover property(
              @(posedge clk)
               (`OVL_RESET_SIGNAL != 1'b0) && bit_vector[g]);
        end : mutex_bitmap

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        cover_no_mutex_bits :
          cover property(
            @(posedge clk)
             (`OVL_RESET_SIGNAL != 1'b0) && (bit_vector == {width{1'b0}}) )
             ovl_cover_t("None of the bits of test expr is asserted (invert_mode=0) or deasserted (invert_mode=1)");

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON
