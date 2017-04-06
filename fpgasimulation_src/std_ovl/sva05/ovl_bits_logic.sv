// Accellera Standard V2.3 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2008. All rights reserved.


`ifdef OVL_ASSERT_ON

  reg    error_min, error_max, error_xz_test_expr;
  wire   error_event, error_event_xz;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    error_min          = 1'b0;
    error_max          = 1'b0;
    error_xz_test_expr = 1'b0;
  end
`endif

  always @(posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b1) begin
      error_min          <= 1'b0;
      error_max          <= 1'b0;
      error_xz_test_expr <= 1'b0;
    end
  end

  assign error_event    =  (error_min | error_max);
  assign error_event_xz =  error_xz_test_expr;

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

  assign bit_vector = (asserted == 1) ? test_expr : (~test_expr);

`endif  //  OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property OVL_BITS_MIN_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      ($countones(bit_vector) >= min);
  endproperty

  property OVL_BITS_MAX_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      ($countones(bit_vector) <= max);
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

      property OVL_BITS_XZ_ON_TEST_EXPR_P;
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

       if (min != 0) begin
          A_OVL_BITS_MIN_P:
          assert property (OVL_BITS_MIN_P)
            error_min <= 1'b0;
          else begin
            if (asserted == 1)
              ovl_error_t(`OVL_FIRE_2STATE,"Fewer than `min' bits were asserted");
            else
              ovl_error_t(`OVL_FIRE_2STATE,"Fewer than `min' bits were deasserted");
            error_min <= 1'b1;
          end
        end

        if (max != 0) begin
          A_OVL_BITS_MAX_P:
          assert property (OVL_BITS_MAX_P)
            error_max <= 1'b0;
          else begin
            if (asserted == 1)
              ovl_error_t(`OVL_FIRE_2STATE,"More than `max' bits were asserted");
            else
              ovl_error_t(`OVL_FIRE_2STATE,"More than `max' bits were deasserted");
            error_max <= 1'b1;
          end
        end 

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_BITS_XZ_ON_TEST_EXPR_P:
        assert property (OVL_BITS_XZ_ON_TEST_EXPR_P)
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

      if (min != 0) begin 
          M_OVL_BITS_MIN_P:
          assume property (OVL_BITS_MIN_P);
      end 

      if (max != 0) begin
          M_OVL_BITS_MAX_P:
          assume property (OVL_BITS_MAX_P);
      end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_BITS_XZ_ON_TEST_EXPR_P:
        assume property (OVL_BITS_XZ_ON_TEST_EXPR_P);

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

        cover_bits_within_limit :
          cover property(
            @(posedge clk)
             ((`OVL_RESET_SIGNAL != 1'b0) &&
              ($countones(bit_vector) >= min) && ($countones(bit_vector) <= max)))
              if (asserted == 1)
                ovl_cover_t("Number of bits on is within specified min to max limit");
              else
                ovl_cover_t("Number of bits off is within specified min to max limit");

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        cover_bits_at_min:
      	  cover property (
            @(posedge clk)
             ((`OVL_RESET_SIGNAL != 1'b0) && ($countones(bit_vector) == min)))
             if (asserted == 1)
               ovl_cover_t("Number of bits on is exactly equal to min");
             else
               ovl_cover_t("Number of bits off is exactly equal to min");

      	cover_bits_at_max:
      	  cover property (
            @(posedge clk)
             ((`OVL_RESET_SIGNAL != 1'b0) && ($countones(bit_vector) == max)))
             if (asserted == 1)
               ovl_cover_t("Number of bits on is exactly equal to max");
             else
               ovl_cover_t("Number of bits off is exactly equal to max");

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON

