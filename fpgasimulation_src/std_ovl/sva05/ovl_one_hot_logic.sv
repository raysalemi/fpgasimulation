// Accellera Standard V2.3 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2008. All rights reserved.

`ifdef OVL_ASSERT_ON

`ifdef OVL_XCHECK_OFF
   wire fire_xcheck = 0;
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
     wire fire_xcheck = 0;
  `else

    property ASSERT_ONE_HOT_XZ_P;
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

  property ASSERT_ONE_HOT_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  !($isunknown(test_expr)) |-> ($onehot(test_expr));
  endproperty

  wire fire_2state;
  reg fire_2state_one_hot;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_2state_one_hot = 1'b0;
  end
`endif

  assign fire_2state = (fire_2state_one_hot) ?
                       ovl_fire_2state_f(property_type) : 1'b0;

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        A_ASSERT_ONE_HOT_P:
        assert property (ASSERT_ONE_HOT_P)
        fire_2state_one_hot <= 1'b0;
        else begin
          ovl_error_t(`OVL_FIRE_2STATE,"Test expression contains more or less than 1 asserted bits");
          fire_2state_one_hot <= 1'b1;
        end
`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_ONE_HOT_XZ_P:
        assert property (ASSERT_ONE_HOT_XZ_P)
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
        M_ASSERT_ONE_HOT_P:    assume property (ASSERT_ONE_HOT_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_ONE_HOT_XZ_P: assume property (ASSERT_ONE_HOT_XZ_P);
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
      fire_cover_all_one_hots_checked;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    fire_cover_test_expr_change = 1'b0;
    fire_cover_all_one_hots_checked = 1'b0;
  end
`endif

  assign fire_cover = (fire_cover_test_expr_change ||
                       fire_cover_all_one_hots_checked) ?
                      ovl_fire_cover_f(coverage_level) : 1'b0;

      wire [width-1:0] test_expr_1 = test_expr - {{width-1{1'b0}},1'b1};
      reg [width-1:0] one_hots_checked;

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

      always @(posedge clk) begin
        if (`OVL_RESET_SIGNAL != 1'b0) begin
          if ((test_expr ^ test_expr)=={width{1'b0}}) begin
            if (!((test_expr == {width{1'b0}}) ||
                  (test_expr & test_expr_1) != {width{1'b0}})) begin
              one_hots_checked <= one_hots_checked | test_expr;
            end
          end
        end
        else begin
`ifdef OVL_INIT_REG
         one_hots_checked <= {width{1'b0}};
`endif
        end
      end // always

      cover_all_one_hots_checked:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) &&
                     $rose(one_hots_checked == {width{1'b1}}) ) ) begin
                       ovl_cover_t("all_one_hots_checked covered");
                       fire_cover_all_one_hots_checked <= 1'b1;
                     end
     end //corner coverage
    end

  endgenerate

`else // OVL_COVER_ON

   wire fire_cover = 0;

`endif // OVL_COVER_ON
