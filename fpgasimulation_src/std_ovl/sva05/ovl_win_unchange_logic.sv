// Accellera Standard V2.3 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2008. All rights reserved.

`ifdef OVL_SHARED_CODE

  reg window = 0;

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      if (!window && start_event == 1'b1)
        window <= 1'b1;
      else if (window && end_event == 1'b1)
        window <= 1'b0;
    end
    else begin
      window <= 1'b0;
    end
  end

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property ASSERT_WIN_UNCHANGE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (start_event && !window) ##1 (!(end_event && $stable(test_expr)))[*1:$] |-> $stable(test_expr);
  endproperty

  wire fire_2state;
  reg fire_2state_win_unchange;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_2state_win_unchange = 1'b0;
  end
`endif

  assign fire_2state = (fire_2state_win_unchange) ?
                       ovl_fire_2state_f(property_type) : 1'b0;

`ifdef OVL_XCHECK_OFF
   wire fire_xcheck = 0;
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
     wire fire_xcheck = 0;
  `else

  property ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  !(window) |-> (!($isunknown(start_event)));
  endproperty

  property ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (window || start_event) |-> (!($isunknown(test_expr)));
  endproperty

  property ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (window) |-> (!($isunknown(end_event)));
  endproperty

  wire fire_xcheck;
  reg fire_xcheck_start_event, fire_xcheck_test_expr, fire_xcheck_end_event;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_xcheck_start_event = 1'b0;
    fire_xcheck_test_expr = 1'b0;
    fire_xcheck_end_event = 1'b0;
  end
`endif

  assign fire_xcheck = (fire_xcheck_start_event ||
                        fire_xcheck_test_expr ||
                        fire_xcheck_end_event) ?
                       ovl_fire_xcheck_f(property_type) : 1'b0;

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        A_ASSERT_WIN_UNCHANGE_P:
          assert property (ASSERT_WIN_UNCHANGE_P)
          fire_2state_win_unchange <= 1'b0;
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"Test expression has changed value before the event window closes");
            fire_2state_win_unchange <= 1'b1;
          end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P:
          assert property (ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P)
          fire_xcheck_start_event <= 1'b0;
          else begin
            ovl_error_t(`OVL_FIRE_XCHECK,"start_event contains X or Z");
            fire_xcheck_start_event <= 1'b1;
          end

        A_ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P:
          assert property (ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P)
          fire_xcheck_test_expr <= 1'b0;
          else begin
            ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
            fire_xcheck_test_expr <= 1'b1;
          end

        A_ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P:
          assert property (ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P)
          fire_xcheck_end_event <= 1'b0;
          else begin
            ovl_error_t(`OVL_FIRE_XCHECK,"end_event contains X or Z");
            fire_xcheck_end_event <= 1'b1;
          end
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_WIN_UNCHANGE_P: assume property (ASSERT_WIN_UNCHANGE_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P:
          assume property (ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P);
        M_ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P:
          assume property (ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P);
        M_ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P:
          assume property (ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P);
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
  reg fire_cover_window_open, fire_cover_window;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_cover_window_open = 1'b0;
    fire_cover_window = 1'b0;
  end
`endif

  assign fire_cover = (fire_cover_window_open ||
                       fire_cover_window) ?
                      ovl_fire_cover_f(coverage_level) : 1'b0;
  
generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
     if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      cover_window_open:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     start_event && !window) ) begin
                       ovl_cover_t("window_open covered");
                       fire_cover_window_open <= 1'b1;
                     end 

      cover_window:
      cover property (@(posedge clk) (`OVL_RESET_SIGNAL != 1'b0) throughout
                     ((start_event && !window) ##1
                     (!end_event && window) [*0:$] ##1
                     (end_event && window)) ) begin
                       ovl_cover_t("window covered");
                       fire_cover_window <= 1'b1;
                     end
     end //basic coverage
    end

endgenerate

`else // OVL_COVER_ON

   wire fire_cover = 0;

`endif // OVL_COVER_ON

