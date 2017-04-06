// Accellera Standard V2.3 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2008. All rights reserved.


`ifdef OVL_ASSERT_ON

  reg    error_overflow, error_underflow, error_push_pop, error_value, error_full, error_empty, error_xz_push, error_xz_pop, error_xz_full, error_xz_empty, error_xz_push_data, error_xz_pop_data;
  wire   error_event, error_event_xz;

`ifdef OVL_SYNTHESIS
`else
 initial
    begin
      error_value=1'b0;
      error_overflow=1'b0;
      error_underflow=1'b0;
      error_push_pop = 1'b0;
      error_full=1'b0;
      error_empty=1'b0;
      error_xz_push=1'b0;
      error_xz_pop=1'b0;
      error_xz_full=1'b0;
      error_xz_empty=1'b0;
      error_xz_push_data=1'b0;
      error_xz_pop_data=1'b0;
    end
`endif

  assign error_event    =  (error_overflow | error_underflow | error_push_pop | error_value |
                            error_full | error_empty);
  assign error_event_xz =  (error_xz_push | error_xz_pop | error_xz_full | error_xz_empty |
                            error_xz_push_data | error_xz_pop_data);

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

  localparam             ptr_width              = log2(depth);

  wire                   sva_v_deferred_pop;
  wire                   sva_v_deferred_push;

  reg   [ptr_width :0]   sva_v_stack_ptr;

  always @( posedge clk)
  begin
    sva_v_stack_ptr <=
      (`OVL_RESET_SIGNAL != 1'b1) ?
        0 :
        (sva_v_deferred_push && sva_v_deferred_pop) ?
          sva_v_stack_ptr :
          (sva_v_deferred_push && (sva_v_stack_ptr < depth)) ?
            sva_v_stack_ptr + 1 :
            (sva_v_deferred_pop && (sva_v_stack_ptr > 0)) ?
              sva_v_stack_ptr - 1 :
              sva_v_stack_ptr;
  end

  generate
    if( pop_latency > 1)
    begin : pop_latency_g_1
      reg   [pop_latency-1 : 0]  sva_v_deferred_pop_sr = 0;
      assign sva_v_deferred_pop = sva_v_deferred_pop_sr[pop_latency-1];
      always @(posedge clk)
      begin
        sva_v_deferred_pop_sr <=
          { sva_v_deferred_pop_sr[pop_latency-2 : 0],pop};
      end
    end : pop_latency_g_1
    if( pop_latency == 1)
    begin : pop_latency_e_1
      reg   sva_v_deferred_pop_sr = 0;
      assign sva_v_deferred_pop = sva_v_deferred_pop_sr;
      always @ (posedge clk)
      begin
        sva_v_deferred_pop_sr <= pop;
      end
    end : pop_latency_e_1
    if( pop_latency == 0)
    begin : pop_latency_e_0
      assign sva_v_deferred_pop = pop;
    end : pop_latency_e_0

    if( push_latency > 1)
    begin : push_latency_g_1
      reg   [push_latency-1 : 0]  sva_v_deferred_push_sr = 0;
      assign sva_v_deferred_push = sva_v_deferred_push_sr[push_latency-1];
      always @(posedge clk)
      begin
        sva_v_deferred_push_sr <=
          { sva_v_deferred_push_sr[push_latency-2 : 0],push};
      end
    end : push_latency_g_1
    if( push_latency == 1)
    begin : push_latency_e_1
      reg   sva_v_deferred_push_sr = 0;
      assign sva_v_deferred_push = sva_v_deferred_push_sr;
      always @ (posedge clk)
      begin
        sva_v_deferred_push_sr <= push;
      end
    end : push_latency_e_1
    if( push_latency == 0)
    begin : push_latency_e_0
      assign sva_v_deferred_push = push;
    end : push_latency_e_0

  endgenerate

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  reg [(width-1) : 0] sva_v_stack [0 : depth];
  wire [(width-1) : 0] sva_w_data;
  assign sva_w_data = sva_v_stack[sva_v_stack_ptr-1];

  always @( posedge clk)
  begin
    sva_v_stack[sva_v_stack_ptr] <=
      (`OVL_RESET_SIGNAL != 1'b1) ?
        0 :
        (sva_v_deferred_push && sva_v_deferred_pop) ?
          sva_v_stack[sva_v_stack_ptr] :
          ((sva_v_stack_ptr < depth) && sva_v_deferred_push) ?
            push_data :
            sva_v_stack[sva_v_stack_ptr];
  end

  property OVL_STACK_OVERFLOW_P;
    @( posedge clk)
      disable iff( `OVL_RESET_SIGNAL != 1'b1)
        not((sva_v_stack_ptr >= depth) &&
          sva_v_deferred_push &&
          (!sva_v_deferred_pop));
  endproperty : OVL_STACK_OVERFLOW_P

  property OVL_STACK_UNDERFLOW_P;
    @( posedge clk)
      disable iff( `OVL_RESET_SIGNAL != 1'b1)
        not((sva_v_stack_ptr == 0) &&
          (!sva_v_deferred_push) &&
          sva_v_deferred_pop );
  endproperty : OVL_STACK_UNDERFLOW_P

  property OVL_STACK_VALUE_P;
    @( posedge clk)
      disable iff( `OVL_RESET_SIGNAL != 1'b1)
       (sva_v_deferred_pop && !sva_v_deferred_push && sva_v_stack_ptr > 0) |->
          (sva_w_data == pop_data );
  endproperty : OVL_STACK_VALUE_P

  property OVL_STACK_PUSH_POP_P;
    @( posedge clk)
      disable iff( `OVL_RESET_SIGNAL != 1'b1)
        not( sva_v_deferred_push &&
             sva_v_deferred_pop);
  endproperty : OVL_STACK_PUSH_POP_P

  property OVL_STACK_EMPTY_P;
    @( posedge clk)
      disable iff( `OVL_RESET_SIGNAL != 1'b1)
        not (( sva_v_stack_ptr == 0 && empty == 1'b0) ||
         ( sva_v_stack_ptr != 0 && empty == 1'b1));
  endproperty : OVL_STACK_EMPTY_P

  property OVL_STACK_FULL_P;
    @( posedge clk)
      disable iff( `OVL_RESET_SIGNAL != 1'b1)
        not (( sva_v_stack_ptr == depth && full == 1'b0) ||
         ( sva_v_stack_ptr != depth && full == 1'b1));
  endproperty : OVL_STACK_FULL_P


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

      property OVL_BITS_XZ_ON_PUSH_P;
          @(posedge clk)
          disable iff (`OVL_RESET_SIGNAL != 1'b1)
          (!($isunknown(push)));
      endproperty

      property OVL_BITS_XZ_ON_POP_P;
          @(posedge clk)
          disable iff (`OVL_RESET_SIGNAL != 1'b1)
          (!($isunknown(pop)));
      endproperty

      property OVL_BITS_XZ_ON_FULL_P;
          @(posedge clk)
          disable iff (`OVL_RESET_SIGNAL != 1'b1)
          (!($isunknown(full)));
      endproperty

      property OVL_BITS_XZ_ON_EMPTY_P;
          @(posedge clk)
          disable iff (`OVL_RESET_SIGNAL != 1'b1)
          (!($isunknown(empty)));
      endproperty

      property OVL_BITS_XZ_ON_PUSH_DATA_P;
          @(posedge clk)
          disable iff (`OVL_RESET_SIGNAL != 1'b1)
          (sva_v_deferred_push && !sva_v_deferred_pop) |-> (!($isunknown(push_data)));
      endproperty

      property OVL_BITS_XZ_ON_POP_DATA_P;
          @(posedge clk)
          disable iff (`OVL_RESET_SIGNAL != 1'b1)
          (sva_v_deferred_pop && !sva_v_deferred_push) |-> (!($isunknown(pop_data)));
      endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT:
	begin : ovl_assert
        A_OVL_STACK_OVERFLOW_P:  assert property (OVL_STACK_OVERFLOW_P)
		                     error_overflow <= 0;
                                 else
			         begin
				     ovl_error_t(`OVL_FIRE_2STATE,"Data is pushed into the stack when the stack is full");
				     error_overflow <= 1;
			         end

        A_OVL_STACK_UNDERFLOW_P: assert property (OVL_STACK_UNDERFLOW_P)
		                     error_underflow <= 0;
                                 else
			         begin
				     ovl_error_t(`OVL_FIRE_2STATE,"Data is poped from the stack when the stack is empty");
				     error_underflow <= 1;
			         end

        A_OVL_STACK_VALUE_P:     assert property (OVL_STACK_VALUE_P)
		                     error_value <= 0;
                                 else
			         begin
				     ovl_error_t(`OVL_FIRE_2STATE,"Data poped from the stack is not the same as the data pushed into the stack");
				     error_value <= 1;
			         end

        A_OVL_STACK_PUSH_POP_P:  assert property (OVL_STACK_PUSH_POP_P)
		                     error_push_pop <= 0;
                                 else
			         begin
				     ovl_error_t(`OVL_FIRE_2STATE,"push and pop are asserted simultaneously");
				     error_push_pop <= 1;
			         end

        A_OVL_STACK_EMPTY_P:     assert property (OVL_STACK_EMPTY_P)
		                     error_empty <= 0;
                                 else
 				     if ( sva_v_stack_ptr == 0 && empty == 1'b0)
			             begin
				         ovl_error_t(`OVL_FIRE_2STATE,"Empty flag is not asserted when the stack is empty");
				         error_empty <= 1;
			             end
				     else
			                 begin
				             ovl_error_t(`OVL_FIRE_2STATE,"Empty flag is asserted when the stack is not empty");
				             error_empty <= 1;
			                 end

        A_OVL_STACK_FULL_P:      assert property (OVL_STACK_FULL_P)
		                     error_full <= 0;
                                 else
				     if ( sva_v_stack_ptr == depth && full == 1'b0)
			             begin
				         ovl_error_t(`OVL_FIRE_2STATE,"Full flag is not asserted when the stack is full");
				         error_full <= 1;
			             end
				     else
					 begin
				             ovl_error_t(`OVL_FIRE_2STATE,"Full flag is asserted when the stack is not full");
				             error_full <= 1;
			                 end

			

  `ifdef OVL_XCHECK_OFF
    //Do nothing
  `else
    `ifdef OVL_IMPLICIT_XCHECK_OFF
      //Do nothing
    `else
        A_OVL_BITS_XZ_ON_PUSH_P:
        assert property (OVL_BITS_XZ_ON_PUSH_P)
	    error_xz_push <= 0;
        else
	begin
	    ovl_error_t(`OVL_FIRE_XCHECK,"push contains X or Z");
	    error_xz_push <= 1;
	end

        A_OVL_BITS_XZ_ON_POP_P:
        assert property (OVL_BITS_XZ_ON_POP_P)
	    error_xz_pop <= 0;
        else
	begin
	    ovl_error_t(`OVL_FIRE_XCHECK,"pop contains X or Z");
	    error_xz_pop <= 1;
	end

        A_OVL_BITS_XZ_ON_FULL_P:
        assert property (OVL_BITS_XZ_ON_FULL_P)
	    error_xz_full <= 0;
        else
	begin
	    ovl_error_t(`OVL_FIRE_XCHECK,"full flag contains X or Z");
	    error_xz_full <= 1;
	end

        A_OVL_BITS_XZ_ON_EMPTY_P:
        assert property (OVL_BITS_XZ_ON_EMPTY_P)
	    error_xz_empty <= 0;
        else
	begin
	    ovl_error_t(`OVL_FIRE_XCHECK,"empty flag contains X or Z");
	    error_xz_empty <= 1;
	end

        A_OVL_BITS_XZ_ON_PUSH_DATA_P:
        assert property (OVL_BITS_XZ_ON_PUSH_DATA_P)
	    error_xz_push_data <= 0;
        else
	begin
	    ovl_error_t(`OVL_FIRE_XCHECK,"push_data contains X or Z");
	    error_xz_push_data <= 1;
	end

        A_OVL_BITS_XZ_ON_POP_DATA_P:
        assert property (OVL_BITS_XZ_ON_POP_DATA_P)
	    error_xz_pop_data <= 0;
        else
	begin
	    ovl_error_t(`OVL_FIRE_XCHECK,"pop_data contains X or Z");
	    error_xz_pop_data <= 1;
	end
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF
      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME:
	begin : ovl_assume
        M_OVL_STACK_OVERFLOW_P:  assume property (OVL_STACK_OVERFLOW_P);
        M_OVL_STACK_UNDERFLOW_P: assume property (OVL_STACK_UNDERFLOW_P);
        M_OVL_STACK_VALUE_P:     assume property (OVL_STACK_VALUE_P);
        M_OVL_STACK_PUSH_POP_P:  assume property (OVL_STACK_PUSH_POP_P);
        M_OVL_STACK_EMPTY_P:     assume property (OVL_STACK_EMPTY_P);
        M_OVL_STACK_FULL_P:      assume property (OVL_STACK_FULL_P);

  `ifdef OVL_XCHECK_OFF
    //Do nothing
  `else
    `ifdef OVL_IMPLICIT_XCHECK_OFF
      //Do nothing
    `else
        M_OVL_BITS_ON_PUSH_P:
        assume property (OVL_BITS_XZ_ON_PUSH_P);

        M_OVL_BITS_ON_POP_P:
        assume property (OVL_BITS_XZ_ON_POP_P);

        M_OVL_BITS_ON_FULL_P:
        assume property (OVL_BITS_XZ_ON_FULL_P);

        M_OVL_BITS_ON_EMPTY_P:
        assume property (OVL_BITS_XZ_ON_EMPTY_P);

        M_OVL_BITS_ON_PUSH_DATA_P:
        assume property (OVL_BITS_XZ_ON_PUSH_DATA_P);

        M_OVL_BITS_ON_POP_DATA_P:
        assume property (OVL_BITS_XZ_ON_POP_DATA_P);
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF
      end

      `OVL_IGNORE :
	begin : ovl_ignore
            // do nothing;
        end

      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase
  endgenerate

`endif // OVL_ASSERT_ON


`ifdef OVL_COVER_ON

  reg                    sva_v_high_water_failed;
  reg   [ptr_width :0]   max_stack_entries;

  always @(posedge clk)
  begin
         sva_v_high_water_failed <=
           ((`OVL_RESET_SIGNAL != 1'b1) || (high_water_mark == 0)) ?
             0 :
           (sva_v_stack_ptr >= high_water_mark);
  end

  always @( posedge clk)
  begin
      max_stack_entries <=
      (`OVL_RESET_SIGNAL != 1'b1 ) ?
        0 :
        (max_stack_entries < sva_v_stack_ptr) ?
          sva_v_stack_ptr :
          max_stack_entries;
  end

  generate
    if (coverage_level != `OVL_COVER_NONE)
    begin : ovl_cover

      if (OVL_COVER_SANITY_ON)
      begin : ovl_cover_sanity
        cover_number_of_pushes:
          cover property (@(posedge clk)
                   ( `OVL_RESET_SIGNAL != 1'b0 && push))
            ovl_cover_t("stack number of push operation covered");

         cover_number_of_pops :
           cover property( @(posedge clk)
                   ( `OVL_RESET_SIGNAL != 1'b0 && pop))
             ovl_cover_t("stack number of pop operation covered");
      end //sanity coverage

      if (OVL_COVER_CORNER_ON)
      begin : ovl_cover_corner
        cover_stack_high_water_mark :
          cover property (@(posedge clk)  ((`OVL_RESET_SIGNAL != 1'b0) &&
		       (sva_v_stack_ptr >= high_water_mark) && high_water_mark && !sva_v_high_water_failed))
                     ovl_cover_t("stack high_water_mark_covered");

        cover_number_of_empty_after_pop:
          cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) throughout
                     ( sva_v_deferred_pop ##1
		       ( !$stable( sva_v_stack_ptr) && ( sva_v_stack_ptr ==0) ) ) ) )
                     ovl_cover_t("stack empty after a pop covered");

        cover_number_of_full_after_push:
          cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) throughout
                     ( sva_v_deferred_push ##1
		       ( !$stable( sva_v_stack_ptr) && ( sva_v_stack_ptr ==depth) ) ) ) )
                     ovl_cover_t("stack full after a push covered");
      end //Corner case Coverage

      if (OVL_COVER_BASIC_ON)
      begin : ovl_cover_basic
        cover_push_followed_eventually_by_pop :
          cover property(@(posedge clk)
                        ((`OVL_RESET_SIGNAL != 1'b0) throughout
                        ( (push && !pop) ##1 !push[*1:$] ##0 pop)))
            ovl_cover_t("stack push followed by pop covered");

        cover_max_stack_entries :
          cover property(@(posedge clk)
                        ((`OVL_RESET_SIGNAL != 1'b0) && !($stable(max_stack_entries)) && max_stack_entries > 0 ))
            ovl_cover_t("maximum entries in stack covered");
      end //Basic coverage

    end:ovl_cover
  endgenerate
`endif

