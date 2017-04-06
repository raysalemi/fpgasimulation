// Accellera Standard V2.3 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2008. All rights reserved.


`ifdef OVL_ASSERT_ON

  reg 	  error_enqueue, error_dequeue, error_full, error_empty;
  reg [deq_count-1:0] error_value,error_xz_detected_deq_data;
  reg 		      error_xz_detected_enq, error_xz_detected_deq, error_xz_detected_full, error_xz_detected_empty;
  reg [enq_count-1:0] error_xz_detected_enq_data;

  wire 		      error_event, error_event_xz;

  assign  error_event    = (error_enqueue | error_dequeue | (|error_value) | error_full | error_empty);

  assign  error_event_xz = (error_xz_detected_enq | error_xz_detected_deq | error_xz_detected_full |
                            error_xz_detected_empty | (|error_xz_detected_enq_data) | (|error_xz_detected_deq_data));

`ifdef OVL_SYNTHESIS
`else
  initial begin 
    error_enqueue            = 1'b0;
    error_dequeue            = 1'b0;
    error_value              = {(deq_count){1'b0}};
    error_full               = 1'b0;
    error_empty              = 1'b0;
    error_xz_detected_enq    = 1'b0;
    error_xz_detected_deq    = 1'b0;
    error_xz_detected_full   = 1'b0;
    error_xz_detected_empty  = 1'b0;
    error_xz_detected_enq_data={(enq_count){1'b0}};
    error_xz_detected_deq_data={(deq_count){1'b0}};
  end
`endif

  always @(posedge clk) begin
    if(`OVL_RESET_SIGNAL == 1'b0)
      begin
        error_enqueue              = 1'b0;
        error_dequeue              = 1'b0;
        error_value                = {(deq_count){1'b0}};
        error_full                 = 1'b0;
        error_empty                = 1'b0;
        error_xz_detected_enq      = 1'b0;
        error_xz_detected_deq      = 1'b0;
        error_xz_detected_full     = 1'b0;
        error_xz_detected_empty    = 1'b0;
        error_xz_detected_enq_data = {(enq_count){1'b0}};
        error_xz_detected_deq_data = {(deq_count){1'b0}};
      end
    end
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

`ifdef OVL_SYNTHESIS
`else
  initial
    begin
      if(enq_count > depth)
	ovl_error_t(`OVL_FIRE_2STATE,"Illegal value for enq_count parameter which must not be greater than the depth");
      if(deq_count > depth)
	ovl_error_t(`OVL_FIRE_2STATE,"Illegal value for deq_count parameter which must not be greater than the depth");
    end
`endif

`ifdef OVL_SHARED_CODE

  // Local parameter for width of variable
  localparam   enq_bw = log2(enq_count);
  localparam   deq_bw = log2(deq_count);
  localparam   addr_bw= log2(depth);
  localparam   enq_data_bw = enq_count*width;
  localparam   deq_data_bw = deq_count*width;
//  localparam   enq_latency_bw = (enq_latency ==0)?1:log2(enq_latency);
//  localparam   deq_latency_bw = (deq_latency ==0)?1:log2(deq_latency);
  localparam   enq_latency_bw = (enq_latency ==0)?1:enq_latency;
  localparam   deq_latency_bw = (deq_latency ==0)?1:deq_latency;
  localparam   preload_bw = preload_count?preload_count*width-1:0;

  // Global variable
  reg [addr_bw+1:0] volume;
  reg [enq_bw:0]    total_enq;
  reg [deq_bw:0]    total_deq;
  reg [enq_bw:0]    total_enq_after_deq;
  reg 	      preload_reg;
  reg [deq_data_bw-1:0] expected_deq_data;
  reg [deq_data_bw-1:0] actual_deq_data;
  reg [deq_count-1:0]   expected_deq;
  reg [enq_count-1:0]   enq_pipe[enq_latency_bw:0];
  reg [deq_count-1:0] 	deq_pipe[deq_latency_bw:0];
  reg [enq_count-1:0] 	enq_lat;
  reg [deq_count-1:0] 	deq_lat;
  reg 			enq_fired; // To disable Value Check
  reg [1:0] 		deq_fired; // To disable Value Check
  integer 	  i,j,k,i1,i2,i3;

  // Initialization of global variable

`ifdef OVL_SYNTHESIS
`else
  initial
    begin
      // Volume initialized with preload count
      volume = preload_count;
      total_enq={(enq_bw+1){1'b0}};
      total_deq={(deq_bw+1){1'b0}};
      total_enq_after_deq={(enq_bw+1){1'b0}};
      if (preload_count)
        preload_reg = 1'b1;
      else
	preload_reg = 1'b0;
      for (i3 = 0; i3 <= enq_latency; i3 = i3 + 1)
	enq_pipe[i3] = {enq_count{1'b0}};
      for (i3 = 0; i3 <= deq_latency; i3 = i3 + 1)
	deq_pipe[i3] = {deq_count{1'b0}};
      enq_lat =0;
      deq_lat =0;
      enq_fired = 1'b0;
      deq_fired = 2'b0;
    end // initial begin
`endif

  // Logic for calculation of valid enq and deq count
  always @(enq or deq or volume or pass_thru or registered or preload_reg or enq_pipe[enq_latency_bw-1] or deq_pipe[deq_latency_bw-1] )
    begin
      enq_lat = (enq_latency==0) ?  enq : enq_pipe[enq_latency_bw-1];
      deq_lat = (deq_latency==0) ?  deq : deq_pipe[deq_latency_bw-1];
      total_enq_after_deq=0;
      if(pass_thru == 0 && registered == 0)
	begin
	  total_enq=($countones(enq_lat) <= depth-volume)?$countones(enq_lat):(depth-volume);
	  total_deq=($countones(deq_lat) <= volume)?$countones(deq_lat):volume;
	end
      else if(pass_thru == 1 && registered == 0)
	begin
	  total_enq=($countones(enq_lat) <= depth-volume)?$countones(enq_lat):(depth-volume);
	  total_deq=($countones(deq_lat) <= volume+total_enq)?$countones(deq_lat):volume+total_enq;
	end
      else if(pass_thru == 0 && registered == 1)
	begin
	  total_deq=($countones(deq_lat) <= volume)?$countones(deq_lat):volume;
	  total_enq=($countones(enq_lat) <= depth-(volume-total_deq))?$countones(enq_lat):(depth-(volume-total_deq));
	end
      else
	begin
	  total_enq=($countones(enq_lat) <= depth-volume)?$countones(enq_lat):(depth-volume);
	  total_deq=($countones(deq_lat) <= volume+total_enq)?$countones(deq_lat):volume+total_enq;
	  total_enq_after_deq=(($countones(enq_lat)-total_enq)<= depth-(volume+total_enq-total_deq)?
			       ($countones(enq_lat)-total_enq):depth-(volume+total_enq-total_deq));
	end // else: !if(pass_thru == 0 && registered == 1)
    end // always @ (enq or deq or volume or pass_thru or registereded or preload_reg)

  // Logic for updating size of fifo(volume), enq_pipe, deq_pipe and coverage variables
  always @(posedge clk )
    begin
      if(`OVL_RESET_SIGNAL != 1'b1)
	begin
	  // Volume initialized with preload count
	  volume <= preload_count;
	  for (i2 = 0; i2 <= enq_latency; i2 = i2 + 1)
	    enq_pipe[i2] <= {enq_count{1'b0}};
	  for (i2 = 0; i2 <= deq_latency; i2 = i2 + 1)
	    deq_pipe[i2] <= {deq_count{1'b0}};
	  if (preload_count)
	    preload_reg <= 1'b1;
	  else
	    preload_reg <= 1'b0;
	  enq_fired <= 1'b0;
	  deq_fired <= 2'b0;
	end
      else
	begin
	  // Calculate volume - number of entries in the fifo
	  volume <= volume +total_enq+total_enq_after_deq-total_deq;
	  // Logic for latching enq based on enq latency
	  if(enq_latency != 0)
	    begin
              for(i2=0;i2<enq_latency;i2=i2+1)
                enq_pipe[i2+1] <= enq_pipe[i2];
	      enq_pipe[0] <= enq;
	    end
	  // deq latency
	  if(deq_latency != 0)
	    begin
              for(i2=0;i2<deq_latency;i2=i2+1)
                deq_pipe[i2+1] <= deq_pipe[i2];
	      deq_pipe[0] <= deq;
	    end
	  deq_fired[1] <= deq_fired[0];
	end // else: !if(`OVL_RESET_SIGNAL != 1'b1)
    end // always @ (posedge clk )
`endif

`ifdef OVL_ASSERT_ON

  // Assert property starts here
  property OVL_MULTIPORT_FIFO_DEQUEUE_CHECK_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (pass_thru== 0)?($countones(deq_lat) <= volume) :($countones(deq_lat) <= volume+total_enq);
  endproperty

  property OVL_MULTIPORT_FIFO_ENQUEUE_CHECK_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (registered== 0)?($countones(enq_lat) <= depth-volume) :($countones(enq_lat) <= depth-(volume-total_deq));
  endproperty

  property OVL_MULTIPORT_FIFO_FULL_CHECK_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      ((full && (volume == depth)) or (!full && (volume != depth)));
  endproperty

  property OVL_MULTIPORT_FIFO_EMPTY_CHECK_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      ((empty && (volume == 0)) or (!empty && (volume != 0)));
  endproperty

  // Argument are passed as this property asserted for deq_count times
  property OVL_MULTIPORT_FIFO_VALUE_CHECK_P(expected_deq_p,expected_deq_data_p,deq_data_p);
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (expected_deq_p && !enq_fired && !deq_fired[1]) |-> expected_deq_data_p == deq_data_p;
  endproperty

 `ifdef OVL_XCHECK_OFF
    // Do nothing
 `else

  `ifdef OVL_IMPLICIT_XCHECK_OFF
    // Do Nothing
  `else

  property OVL_MULTIPORT_FIFO_XZ_ON_ENQ_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(enq)));
  endproperty

  property OVL_MULTIPORT_FIFO_XZ_ON_DEQ_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(deq)));
  endproperty

  property OVL_MULTIPORT_FIFO_XZ_ON_FULL_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(full)));
  endproperty

  property OVL_MULTIPORT_FIFO_XZ_ON_EMPTY_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(empty)));
  endproperty

  // Argument are passed as this property asserted for enq_count times
  property OVL_MULTIPORT_FIFO_XZ_ON_ENQ_DATA_P(enq_p,enq_data_p);
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
     enq_p |-> (!($isunknown(enq_data_p)));
  endproperty

  // Argument are passed as this property asserted for deq_count times
  property OVL_MULTIPORT_FIFO_XZ_ON_DEQ_DATA_P(deq_p,deq_data_p);
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
     deq_p |-> (!($isunknown(deq_data_p)));
  endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
 `endif // OVL_XCHECK_OFF

    // Checker assertion code begin here
  generate
    genvar gen_i,gen_j,gen_k;
    // Logic for value check
    if(value_check)
      begin: value_checking
	// Implementing SV FIFO
	reg [width-1:0] fifo [depth-1:0];
	// Local variables
	reg [preload_bw:0] preload_data;
	reg [deq_bw:0] 		deq_cnt;
	reg [enq_bw:0] 		enq_cnt;
	reg [enq_data_bw-1:0] 	enq_data_reg;
	reg [enq_count-1:0] 		enq_reg;
	reg [deq_count-1:0] 		deq_reg;
	reg [deq_data_bw-1:0] 	store_expected_deq_data;
	reg [deq_count-1:0] 		valid_deq;
	integer 			fifo_ptr;
	reg                             temp_f;

	function push_back;
          input [width-1:0] push_data;
        begin
          if(fifo_ptr<depth)
	    begin
	      fifo[fifo_ptr]=push_data;
	      fifo_ptr=fifo_ptr+1;
	    end
	end
	endfunction

	function [width-1:0] pop_front;
          input [31:0] w;
        begin
	  if(fifo_ptr>0)
	    begin
              pop_front=fifo[0];
	      for(w=0;w<depth-1;w=w+1)
		fifo[w]=fifo[w+1];
	      fifo_ptr=fifo_ptr-1;
	    end
	end
	endfunction
	// Initialization of local variables
`ifdef OVL_SYNTHESIS
`else
	initial
	  begin
	    store_expected_deq_data = {deq_data_bw{1'b0}};
	    valid_deq = {deq_count{1'b0}};
	    fifo_ptr=0;
	    expected_deq={{deq_count}{1'b0}};
	    expected_deq_data={{deq_data_bw}{1'b0}};
	  end
`endif
        // Logic for enq-deq data in FIFO
	always @(posedge clk )
	  begin
	    if(`OVL_RESET_SIGNAL != 1'b1)
	      begin
		store_expected_deq_data = {deq_data_bw{1'b0}};
		valid_deq = {deq_count{1'b0}};
		fifo_ptr = 0;
		expected_deq_data <= {{deq_data_bw}{1'b0}};
		expected_deq = {{deq_count}{1'b0}};
	      end
	    else
	      begin
		// Preloading
		if (preload_reg == 1'b1)
	          begin
                    preload_data = preload;
                    // Write enq_data into FIFO
                    for (i=0;i<preload_count;i=i+1)
                      begin
                        temp_f = push_back(preload_data[width-1:0]);
                        preload_data = preload_data >> width;
                      end
		    preload_reg <= 1'b0;
		  end
		deq_cnt = {(deq_bw+1){1'b0}};
		enq_cnt = {(enq_bw+1){1'b0}};
				
		enq_data_reg = enq_data;
		enq_reg = (enq_latency==0) ?  enq : enq_pipe[enq_latency_bw-1];
		deq_reg = (deq_latency==0) ?  deq : deq_pipe[deq_latency_bw-1];
		if(pass_thru == 0 && registered == 0)
		  begin
		    // FIFO write
		    for (i=0;i<enq_count;i=i+1)
		      begin
			if (enq_reg[i] == 1'b1 && enq_cnt < total_enq)
			  begin
			    temp_f=push_back(enq_data_reg[width-1:0]);
			    enq_cnt = enq_cnt+1;
			  end
			enq_data_reg = enq_data_reg >> width;
		      end
		    // FIFO read
		    for (i=0;i<deq_count;i=i+1)
		      begin
			store_expected_deq_data = store_expected_deq_data >> width;
			if(deq_reg[i] == 1'b1 && deq_cnt < total_deq)
			  begin
			    store_expected_deq_data[deq_data_bw-1:deq_data_bw-width] = pop_front(0);
			    valid_deq[i] = 1'b1;
			    deq_cnt = deq_cnt+1;
			  end
			else
                          valid_deq[i] = 1'b0;
		      end
                  end
		else if(pass_thru == 1 && registered == 0)
		  begin
		    // FIFO write
		    for (i=0;i<enq_count;i=i+1)
		      begin
			if (enq_reg[i] == 1'b1 && enq_cnt < total_enq)
			  begin
			    temp_f=push_back(enq_data_reg[width-1:0]);
			    enq_cnt = enq_cnt+1;
			  end
			enq_data_reg = enq_data_reg >> width;
		      end
		    // FIFO read
		    for (i=0;i<deq_count;i=i+1)
		      begin
			store_expected_deq_data = store_expected_deq_data >> width;
			if(deq_reg[i] == 1'b1 && deq_cnt < total_deq)
			  begin
			    store_expected_deq_data[deq_data_bw-1:deq_data_bw-width] = pop_front(0);
			    valid_deq[i] = 1'b1;
			    deq_cnt = deq_cnt+1;
			  end
			else
                          valid_deq[i] = 1'b0;
		      end // for (i=0;i<deq_count;i=i+1)
		  end
		else if(pass_thru == 0 && registered == 1)
		  begin
		    // FIFO read
		    for (i=0;i<deq_count;i=i+1)
		      begin
			store_expected_deq_data = store_expected_deq_data >> width;
			if(deq_reg[i] == 1'b1 && deq_cnt < total_deq)
			  begin
			    store_expected_deq_data[deq_data_bw-1:deq_data_bw-width] = pop_front(0);
			    valid_deq[i] = 1'b1;
			    deq_cnt = deq_cnt+1;
			  end
			else
                          valid_deq[i] = 1'b0;
		      end // for (i=0;i<deq_count;i=i+1)
		    // FIFO write
		    for (i=0;i<enq_count;i=i+1)
		      begin
			if (enq_reg[i] == 1'b1 && enq_cnt < total_enq)
			  begin
			    temp_f=push_back(enq_data_reg[width-1:0]);
			    enq_cnt = enq_cnt+1;
			  end
			enq_data_reg = enq_data_reg >> width;
		      end
		
		  end
		else
		  begin
		    // FIFO write
		    for (i=0;i<enq_count;i=i+1)
		      begin
			if (enq_reg[i] == 1'b1 && enq_cnt < total_enq)
			  begin
			    temp_f=push_back(enq_data_reg[width-1:0]);
			    enq_cnt = enq_cnt+1;
			  end
			enq_data_reg = enq_data_reg >> width;
		      end
		    // FIFO read
		    for (i=0;i<deq_count;i=i+1)
		      begin
			store_expected_deq_data = store_expected_deq_data >> width;
			if(deq_reg[i] == 1'b1 && deq_cnt < total_deq)
			  begin
			    store_expected_deq_data[deq_data_bw-1:deq_data_bw-width] = pop_front(0);
			    valid_deq[i] = 1'b1;
			    deq_cnt = deq_cnt+1;
			  end
			else
                          valid_deq[i] = 1'b0;
		      end // for (i=0;i<deq_count;i=i+1)
		    enq_cnt = {(enq_bw+1){1'b0}};
		    // FIFO write again
		    for (i=i;i<enq_count;i=i+1)
		      begin
			if (enq_reg[i] == 1'b1 && enq_cnt < total_enq_after_deq)
			  begin
			    temp_f=push_back(enq_data_reg[width-1:0]);
			    enq_cnt = enq_cnt+1;
			  end
			enq_data_reg = enq_data_reg >> width;
		      end			
		  end
		expected_deq_data <= store_expected_deq_data;
		actual_deq_data <= deq_data;
		expected_deq <=  valid_deq;
              end // else: !if(`OVL_RESET_SIGNAL != 1'b1)
	  end // always @ (posedge clk )

  end // if (value_check)

    // Assertions
    case(property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT:
	begin : ovl_assert
	  if(pass_thru == 0)
	    begin : dequeue_check_p
	      A_OVL_MULTIPORT_FIFO_DEQUEUE_CHECK_P:
		assert property (OVL_MULTIPORT_FIFO_DEQUEUE_CHECK_P)
		  error_dequeue <= 1'b0;
             else
	       begin
		 ovl_error_t(`OVL_FIRE_2STATE,"A dequeue occurred while the FIFO was empty");
		 error_dequeue <= 1'b1;
		 deq_fired[0] <= 1'b1;
	       end
	    end
	  else
	    begin : else_dequeue_check_p
	      A_OVL_MULTIPORT_FIFO_DEQUEUE_CHECK_P:
              assert property (OVL_MULTIPORT_FIFO_DEQUEUE_CHECK_P)
	      error_dequeue <= 1'b0;
             else
	       begin
		 ovl_error_t(`OVL_FIRE_2STATE,"While the FIFO was empty, a dequeue occurred without an enqueue in the same cycle");
		 error_dequeue <= 1'b1;
		 deq_fired[0] <= 1'b1;
	       end
	    end // else: !if(pass_thru == 0)
	  if(registered == 0)
	    begin : enqueue_check_p
	      A_OVL_MULTIPORT_FIFO_ENQUEUE_CHECK_P:
		assert property (OVL_MULTIPORT_FIFO_ENQUEUE_CHECK_P)
		  error_enqueue <= 1'b0;
             else
	       begin
		 ovl_error_t(`OVL_FIRE_2STATE,"An enqueue occurred while the FIFO was full");
		 error_enqueue <= 1'b1;
		 enq_fired <= 1'b1;
	       end
	    end
	  else
	    begin : else_enqueue_check_p
	      A_OVL_MULTIPORT_FIFO_ENQUEUE_CHECK_P:
              assert property (OVL_MULTIPORT_FIFO_ENQUEUE_CHECK_P)
	      error_enqueue <= 1'b0;
             else
	       begin
		 ovl_error_t(`OVL_FIRE_2STATE,"while the FIFO was full, an enqueue occurred without a dequeue in the same cycle");
		 error_enqueue <= 1'b1;
		 enq_fired <= 1'b1;
	       end
	    end // else: !if(registered == 0)
	  if(full_check)
	    begin : full_check_p
	      A_OVL_MULTIPORT_FIFO_FULL_CHECK_P:
		assert property (OVL_MULTIPORT_FIFO_FULL_CHECK_P)
		  error_full <= 1'b0;
              else
		begin
		  if(full)
		    ovl_error_t(`OVL_FIRE_2STATE,"The FIFO was not full when the full signal was asserted");
		  else
		    ovl_error_t(`OVL_FIRE_2STATE,"The full signal was not asserted when the FIFO was full");
		  error_full <= 1'b1;
		end // else: !if(`OVL_RESET_SIGNAL != 1'b1)
	    end // if (full_check)
	  if(empty_check)
	    begin : empty_check_p
	      A_OVL_MULTIPORT_FIFO_EMPTY_CHECK_P:
		assert property (OVL_MULTIPORT_FIFO_EMPTY_CHECK_P)
		  error_empty <= 1'b0;
              else
		begin
		  if(empty)
		    ovl_error_t(`OVL_FIRE_2STATE,"The FIFO was not empty when the empty signal was asserted");
		  else
		    ovl_error_t(`OVL_FIRE_2STATE,"The empty signal was not asserted when the FIFO was empty");
		  error_empty <= 1'b1;
		end // else: !if(`OVL_RESET_SIGNAL != 1'b1)
	    end
	  if(value_check)
	    begin : value_check_p
	      for(gen_i=0;gen_i<deq_count;gen_i=gen_i+1)
		begin : loop_value_check_p
		  A_OVL_MULTIPORT_FIFO_VALUE_CHECK_P:
		    assert property (OVL_MULTIPORT_FIFO_VALUE_CHECK_P
				     (expected_deq[gen_i],expected_deq_data[(gen_i+1)*width-1:gen_i*width],actual_deq_data[(gen_i+1)*width-1:gen_i*width]))
		      error_value[gen_i]<=1'b0;
	          else
		    begin
		      ovl_error_t(`OVL_FIRE_2STATE,"Dequeued FIFO value did not equal the corresponding enqueued value");
		      error_value[gen_i]<=1'b1;
		    end
	      	end // for (gen_i=0;gen_i<deq_count;gen_i=gen_i+1)
	    end // if (value_check)
	
 `ifdef OVL_XCHECK_OFF
	  //Do nothing
 `else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
	  //Do nothing
  `else
	
	  A_OVL_MULTIPORT_FIFO_XZ_ON_ENQ_P:
            assert property (OVL_MULTIPORT_FIFO_XZ_ON_ENQ_P)
	      error_xz_detected_enq <= 1'b0;
             else
	       begin
		 ovl_error_t(`OVL_FIRE_XCHECK,"enq contains X or Z");
		error_xz_detected_enq <= 1'b1;
	      end
	
	  A_OVL_MULTIPORT_FIFO_XZ_ON_DEQ_P:
            assert property (OVL_MULTIPORT_FIFO_XZ_ON_DEQ_P)
              error_xz_detected_deq <= 1'b0;
            else begin
	      ovl_error_t(`OVL_FIRE_XCHECK,"deq contains X or Z");
	      error_xz_detected_deq <= 1'b1;
	    end
	  if(full_check)
	    begin : xz_on_full_p
	      A_OVL_MULTIPORT_FIFO_XZ_ON_FULL_P:
		assert property (OVL_MULTIPORT_FIFO_XZ_ON_FULL_P)
		  error_xz_detected_full <= 1'b0;
                else begin
		  ovl_error_t(`OVL_FIRE_XCHECK,"full contains X or Z");
		  error_xz_detected_full <= 1'b1;
		end
	    end
	  if(empty_check)
	    begin : xz_on_empty_p
	      A_OVL_MULTIPORT_FIFO_XZ_ON_EMPTY_P:
		assert property (OVL_MULTIPORT_FIFO_XZ_ON_EMPTY_P)
		  error_xz_detected_empty<= 1'b0;
                else begin
		  ovl_error_t(`OVL_FIRE_XCHECK,"empty contains X or Z");
		  error_xz_detected_empty <= 1'b1;
		end
	    end
	
	  for(gen_j=0;gen_j<enq_count;gen_j=gen_j+1)
	    begin : xz_on_enq_data_p
	      A_OVL_MULTIPORT_FIFO_XZ_ON_ENQ_DATA_P:
		assert property (OVL_MULTIPORT_FIFO_XZ_ON_ENQ_DATA_P
				 (enq_lat[gen_j],enq_data[gen_j]))
		  error_xz_detected_enq_data[gen_j] <= 1'b0;
	        else  begin
		  ovl_error_t(`OVL_FIRE_XCHECK,"enq_data contains X or Z");
		  error_xz_detected_enq_data[gen_j]<= 1'b1;
		end
	    end // for (gen_j=0;gen_j<enq_count;gen_j=gen_j+1)
	  for(gen_k=0;gen_k<deq_count;gen_k=gen_k+1)
	    begin : xz_on_deq_data_p
	      A_OVL_MULTIPORT_FIFO_XZ_ON_DEQ_DATA_P:
		assert property (OVL_MULTIPORT_FIFO_XZ_ON_DEQ_DATA_P
				 (deq_lat[gen_k],deq_data[gen_k]))
		  error_xz_detected_deq_data[gen_k] <= 1'b0;
	        else  begin
		  ovl_error_t(`OVL_FIRE_XCHECK,"deq_data contains X or Z");
		  error_xz_detected_deq_data[gen_k]<= 1'b1;
		end
	    end // for (gen_k=0;gen_k<deq_count;gen_k=gen_k+1)
  `endif // OVL_IMPLICIT_XCHECK_OFF
 `endif // OVL_XCHECK_OFF
	end // block: ovl_assert

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME:
	begin :ovl_assume
	  M_OVL_MULTIPORT_FIFO_DEQUEUE_CHECK_P:
	    assume property (OVL_MULTIPORT_FIFO_DEQUEUE_CHECK_P);
	  M_OVL_MULTIPORT_FIFO_ENQUEUE_CHECK_P:
	    assume property (OVL_MULTIPORT_FIFO_ENQUEUE_CHECK_P);
	  if(full_check)
	    begin : assume_full_check
	      M_OVL_MULTIPORT_FIFO_FULL_CHECK_P:
		assume property (OVL_MULTIPORT_FIFO_FULL_CHECK_P);
	    end
	  if(empty_check)
	    begin : assume_empty_check
	      M_OVL_MULTIPORT_FIFO_EMPTY_CHECK_P:
		assume property (OVL_MULTIPORT_FIFO_EMPTY_CHECK_P);
	    end
	  if(value_check)
	    begin : assume_value_check
	      for(gen_i=0;gen_i<deq_count;gen_i=gen_i+1)
		begin : assume_loop_value_check_p
		  M_OVL_MULTIPORT_FIFO_VALUE_CHECK_P:
		    assume property (OVL_MULTIPORT_FIFO_VALUE_CHECK_P
				     (expected_deq[gen_i],expected_deq_data[(gen_i+1)*width-1:gen_i*width],actual_deq_data[(gen_i+1)*width-1:gen_i*width]));
		
		end
	    end // if (value_check)
	  	
 `ifdef OVL_XCHECK_OFF
	  //Do nothing
 `else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
	  //Do nothing
  `else
	  M_OVL_MULTIPORT_FIFO_XZ_ON_ENQ_P:
            assume property (OVL_MULTIPORT_FIFO_XZ_ON_ENQ_P);
	  M_OVL_MULTIPORT_FIFO_XZ_ON_DEQ_P:
            assume property (OVL_MULTIPORT_FIFO_XZ_ON_DEQ_P);
	  if(full_check)
	    begin : assume_xz_on_full
	      M_OVL_MULTIPORT_FIFO_XZ_ON_FULL_P:
		assume property (OVL_MULTIPORT_FIFO_XZ_ON_FULL_P);
	    end
	  if(empty_check)
	    begin : assume_xz_on_empty
	      M_OVL_MULTIPORT_FIFO_XZ_ON_EMPTY_P:
		assume property (OVL_MULTIPORT_FIFO_XZ_ON_EMPTY_P);
	    end
	  for(gen_j=0;gen_j<enq_count;gen_j=gen_j+1)
	    begin : assume_xz_on_enq_data
	      M_OVL_MULTIPORT_FIFO_XZ_ON_ENQ_DATA_P:
		assume property (OVL_MULTIPORT_FIFO_XZ_ON_ENQ_DATA_P
				 (enq_lat[gen_j],enq_data[gen_j]));
	    end
	  for(gen_k=0;gen_k<deq_count;gen_k=gen_k+1)
	    begin : assume_xz_on_deq_data
	      M_OVL_MULTIPORT_FIFO_XZ_ON_DEQ_DATA_P:
		assume property (OVL_MULTIPORT_FIFO_XZ_ON_DEQ_DATA_P
				 (deq_lat[gen_k],deq_data[gen_k]));
	    end
		
  `endif // OVL_IMPLICIT_XCHECK_OFF
 `endif // OVL_XCHECK_OFF
	
	end // block: ovl_assume
      `OVL_IGNORE:
	begin :ovl_ignore
	  // Do Nothing;
	end
      default :
	begin
	  initial
	    ovl_error_t(`OVL_FIRE_2STATE,"");
        end
    endcase // case(property_type)
  endgenerate
`endif // OVL_ASSERT_ON


`ifdef OVL_COVER_ON

 `ifdef OVL_COVERGROUP_ON
  // Fifo statistics info
  integer 		  enqueueCount;
  integer 		  dequeueCount;
  integer 		  highWaterCount;
  integer 		  emptyCount;
  integer 		  fullCount;
  integer 		  maxVolume;
  integer 		  currVolume;
  reg [addr_bw+1:0] 	  volume_reg;
  reg 		  high_water_mark_reached;
  reg 		  full_reached;
  reg 		  empty_reached;
  reg 		  initial_empty;
  reg             initial_time;
  integer 	  cov_i;

`ifdef OVL_SYNTHESIS
`else
 initial
   begin
     enqueueCount = 0;
     dequeueCount = 0;
     highWaterCount = 0;
     emptyCount = 0;
     fullCount = 0;
     maxVolume = 0;
     currVolume = 0;
     high_water_mark_reached=1'b0;
     full_reached=1'b0;
     empty_reached=1'b1;
     initial_empty=1'b1;
     initial_time=1'b1;
   end
`endif

  always @(posedge clk )
    begin
      if(`OVL_RESET_SIGNAL != 1'b1)
	begin
	  high_water_mark_reached=1'b0;
	  full_reached=1'b0;
	  empty_reached=1'b1;
	  initial_empty=1'b1;
	end
      else
	begin
	  initial_time<=1'b0;
	  volume_reg = volume +total_enq+total_enq_after_deq-total_deq;
	  if(volume_reg)
	    initial_empty=1'b0;
	
	  enqueueCount <= enqueueCount + $countones(enq);
	  dequeueCount <= dequeueCount + $countones(deq);
	  if(volume_reg  == depth && !full_reached)
	    begin
	      fullCount<=fullCount+1;
	      full_reached=1'b1;
	    end
	  if(volume_reg  <depth)
	    full_reached=1'b0;
	  if(volume_reg  == 0 && !empty_reached)
	    begin
	      emptyCount<=emptyCount+1;
	      empty_reached=1'b1;
	    end
	  if(volume_reg >0)
	    empty_reached=1'b0;

	  maxVolume <= (volume_reg > maxVolume) ? volume_reg : maxVolume;
	  currVolume <= volume_reg;
	  if(volume_reg >= high_water_mark && !high_water_mark_reached && high_water_mark)
	    begin
	      highWaterCount <= highWaterCount + 1;
	      high_water_mark_reached=1'b1;
	    end
	  if(volume_reg < high_water_mark)
	    high_water_mark_reached=1'b0;
	end // else: !if(`OVL_RESET_SIGNAL != 1'b1)
    end // always @ (posedge clk )

// Covergroup starts here
  covergroup OVL_MULTIPORT_FIFO_CORNER @ (posedge clk);
  full : coverpoint (!($stable(fullCount, @ (posedge clk))) && !initial_time)
    iff ($past(`OVL_RESET_SIGNAL,1,,@(posedge clk)) != 1'b0)
      {
       bins cov_fifo_full_count = {1};
       option.at_least = 1;
       option.comment = "Fifo full count";
       }
  empty : coverpoint (!($stable(emptyCount, @ (posedge clk))) && !initial_time)
    iff ($past(`OVL_RESET_SIGNAL,1,,@(posedge clk)) != 1'b0)
      {
       bins cov_fifo_empty_count = {1};
       option.at_least = 1;
       option.comment = "Fifo empty count";
       }
  high_water_mark : coverpoint (!($stable(highWaterCount, @ (posedge clk))) && !initial_time)
    iff ($past(`OVL_RESET_SIGNAL,1,,@(posedge clk)) != 1'b0)
      {
       bins cov_high_water_mark_count = {1};
       option.at_least = 1;
       option.comment = "High water count";
       }
  endgroup

  covergroup OVL_MULTIPORT_FIFO_STATISTIC @ (posedge clk);
  curr_volume : coverpoint (!($stable(currVolume, @ (posedge clk))) && !initial_time)
    iff ($past(`OVL_RESET_SIGNAL,1,,@(posedge clk)) != 1'b0 )
      {
       bins cov_observed_fifo_contents = {1};
       option.at_least = 1;
       option.comment = "Current fifo entry";
       }
  endgroup 		

 `endif //OVL_COVERGROUP_ON
  generate
    genvar g1,g2,g3;
    if (coverage_level != `OVL_COVER_NONE)
      begin : ovl_cover
	if(OVL_COVER_SANITY_ON)
	  begin :ovl_cover_sanity
	    for( g1=0; g1<enq_count; g1=g1+1)
	      begin : cover_no_of_enqueues
		cov_no_of_enqueues :
		  cover property(
				  @(posedge clk)
				  ((`OVL_RESET_SIGNAL != 1'b0) && enq[g1]))
				  ovl_cover_t("enqueue is done");		
	      end
	    for( g2=0; g2<deq_count; g2=g2+1)
	      begin : cover_no_of_deueues
		cov_no_of_dequeues :
		  cover property(
				  @(posedge clk)
				  ((`OVL_RESET_SIGNAL != 1'b0) && deq[g2]))
				  ovl_cover_t("dequeue is done");		
	      end
	  end : ovl_cover_sanity
	
	if(OVL_COVER_BASIC_ON)
	  begin:ovl_cover_basic
	    cov_simultaneous_enq_deq :
	      cover property(
			      @(posedge clk)
			      ((`OVL_RESET_SIGNAL != 1'b0) && enq_lat && deq_lat))
		ovl_cover_t("Simultaneously enqueues and dequeues");		
	  end
	
	if(OVL_COVER_CORNER_ON)
	  begin:ovl_cover_corner
 `ifdef OVL_COVERGROUP_ON
	    OVL_MULTIPORT_FIFO_CORNER MULTIPORT_FIFO_CORNER = new();
 `endif
	
	    cov_simultaneous_enq_deq_when_empty :
		  cover property(
				  @(posedge clk)
				  ((`OVL_RESET_SIGNAL != 1'b0) && enq_lat && deq_lat && volume == 0))
		ovl_cover_t("Simultaneously enqueues and dequeues when fifo empty");
	    cov_simultaneous_enq_deq_when_full :
		  cover property(
				  @(posedge clk)
				  ((`OVL_RESET_SIGNAL != 1'b0) && enq_lat && deq_lat && volume == depth))
		ovl_cover_t("Simultaneously enqueues and dequeues when fifo full");
	
         end // block: ovl_cover_corner
	if(OVL_COVER_STATISTIC_ON)
	  begin:ovl_cover_statistic
 `ifdef OVL_COVERGROUP_ON
	    OVL_MULTIPORT_FIFO_STATISTIC MULTIPORT_FIFO_STATISTIC = new();
 `endif
	  end
      end // ovl_cover
  endgenerate

`endif




