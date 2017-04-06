//----------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

virtual class ovm_sequence #(type REQ = ovm_sequence_item,
                             type RSP = REQ) extends ovm_sequence_base;

typedef ovm_sequencer_param_base #(REQ, RSP) sequencer_t;

sequencer_t        param_sequencer;
REQ                req;
RSP                rsp;
local RSP          response_queue[$];
protected integer      response_queue_depth = 8;
protected bit          response_queue_error_report_disabled = 0;

  function new (string name = "ovm_sequence", 
                ovm_sequencer_base sequencer_ptr = null, 
                ovm_sequence_base parent_seq = null);
    super.new(name);
    if (sequencer_ptr != null) begin
      ovm_report_handler::ovm_report_deprecated("ovm_sequence::new (direct usage of and specifying a sequencer)");
      m_sequencer = sequencer_ptr;
    end
    if (parent_seq != null) begin
      ovm_report_handler::ovm_report_deprecated("ovm_sequence::new (direct usage of and specifying a sequence)");
      m_parent_sequence = parent_seq;
    end
  endfunction // new

  function void do_print (ovm_printer printer);
    super.do_print(printer);
    printer.print_object("req", req);
    printer.print_object("rsp", rsp);
  endfunction

  virtual task start (ovm_sequencer_base sequencer,
              ovm_sequence_base parent_sequence = null,
              integer this_priority = 100,
              bit call_pre_post = 1);

    m_sequence_state_prebody  = 0;
    m_sequence_state_body     = 0;
    m_sequence_state_postbody = 0;
    m_sequence_state_ended    = 0;
    m_sequence_state_stopped  = 0;

    super.start(sequencer, parent_sequence, this_priority, call_pre_post);
    m_set_p_sequencer();

    if (m_sequencer != null) begin
      if (m_sequencer.recording_detail != OVM_NONE) begin
        if (m_parent_sequence == null) begin
          m_tr_handle = m_sequencer.begin_tr(this, get_name());
        end else begin
          m_tr_handle = m_sequencer.begin_child_tr(this, m_parent_sequence.m_tr_handle, 
                                                   get_root_sequence_name());
        end
      end
    end

    // Ensure that the sequence_id is intialized in case this sequence has been stopped previously
    set_sequence_id(-1);
    // Remove all sqr_seq_ids
    m_sqr_seq_ids.delete();

    ->started;
    
    if (call_pre_post == 1) begin
      m_sequence_state = PRE_BODY;
      m_sequence_state_prebody = 1;
      this.pre_body();
    end

    if (parent_sequence != null) begin
      parent_sequence.pre_do(0);
      parent_sequence.mid_do(this);
    end

    m_sequence_state = BODY;
    m_sequence_state_body = 1;
    
`ifndef INCA
    
    fork
      begin
        m_sequence_process = process::self();
        body();
        m_sequence_state_ended = 1;
        m_sequence_state = ENDED;
      end
    join
    
`else
    
    fork //wrap the fork/join_any to only effect this block
      begin
        fork
          begin
            body();
            m_sequence_state_ended = 1;
            m_sequence_state = ENDED;
          end
          begin
            m_sequence_started = 1;
            @m_kill_event;
          end
        join_any
        disable fork;
      end
    join
        
`endif
        
    if (parent_sequence != null) begin
      parent_sequence.post_do(this);
    end

    if (call_pre_post == 1) begin
      m_sequence_state = POST_BODY;
      m_sequence_state_postbody = 1;
      post_body();
    end

    ->ended;
    m_sequence_state = FINISHED;

    if (m_sequencer != null) begin      
      if (m_sequencer.recording_detail != OVM_NONE) begin
        m_sequencer.end_tr(this);
      end
    end

    // Clean up any sequencer queues after exiting
    if (m_sequencer != null) begin
      m_sequencer.sequence_exiting(this);
    end
  endtask // start

  function void send_request(ovm_sequence_item request, bit rerandomize = 0);
    REQ m_request;
    
    assert (m_sequencer != null);
    assert ($cast(m_request, request));

    if (m_request.get_transaction_id() == -1) begin
      m_request.set_transaction_id(m_next_transaction_id++);
    end
    m_sequencer.send_request(this, m_request, rerandomize);
  endfunction // void

  function REQ get_current_item();
    assert($cast(param_sequencer, m_sequencer));
    return (param_sequencer.get_current_item());
  endfunction // REQ

  task get_response(output RSP response, input integer transaction_id = -1);
    integer queue_size, i;

    if (response_queue.size() == 0) begin
      wait (response_queue.size() != 0);
    end

    if (transaction_id == -1) begin
      response = response_queue.pop_front();
      return;
    end

    forever begin
      queue_size = response_queue.size();
      for (i = 0; i < queue_size; i++) begin
        if (response_queue[i].get_transaction_id() == transaction_id) 
          begin
            response = response_queue[i];
            response_queue.delete(i);
            return;
          end
      end
      wait (response_queue.size() != queue_size);
    end
  endtask // get_response

  virtual function void put_response(ovm_sequence_item response_item);
    RSP response;

    assert($cast(response, response_item));
    if ((response_queue_depth == -1) ||
        (response_queue.size() < response_queue_depth)) begin
      response_queue.push_back(response);
      return;
    end
    if (response_queue_error_report_disabled == 0) begin
      ovm_report_error(get_full_name(), "Response queue overflow, response was dropped");
    end
  endfunction // put_response

  virtual function void set_sequencer(ovm_sequencer_base sequencer);
    m_sequencer = sequencer;
    m_set_p_sequencer();
  endfunction // void

  ////////////////////////////////////////////////////////////
  //
  // function void set_response_queue_error_report_disabled(bit value);
  //
  // By default, if the response_queue overflows, an error is reported.
  //
  // The response_queue will overflow if more responses are sent to
  // this sequence from the driver than get_response() calls are made.
  //
  // The error may be disabled by calling 
  //   set_response_queue_error_report_disabled(1).
  //
  // The error may be enabled by calling 
  //   set_response_queue_error_report_disabled(0).
  //
  ////////////////////////////////////////////////////////////

  function void set_response_queue_error_report_disabled(bit value);
    response_queue_error_report_disabled = value;
    endfunction

  ////////////////////////////////////////////////////////////
  //
  // function bit get_response_queue_error_report_disabled();
  //
  // The current value of the response_queue_error_report_disabled
  // bit may be examined with this method.
  //
  // When this bit is 0 (default value), error reports are generated
  // if the response queue overflows.
  //
  // When this bit is 1, no error reports are generated
  //
  ////////////////////////////////////////////////////////////

  function bit get_response_queue_error_report_disabled();
    return(response_queue_error_report_disabled);
  endfunction // bit

  ////////////////////////////////////////////////////////////
  //
  //  function void set_response_queue_depth(integer value);
  //
  //  The default maximum depth of the response queue is 8.  This
  //  method is used to change the maximum depth of the response
  //  queue.
  //
  //  Setting the response_queue_depth to -1 indicates an arbitrarily
  //  deep response queue.  No checking is done
  //
  ////////////////////////////////////////////////////////////

  function void set_response_queue_depth(integer value);
    response_queue_depth = value;
  endfunction  

  ////////////////////////////////////////////////////////////
  //
  //  function integer get_response_queue_depth();
  //
  //  This method returns the current response_queue_depth
  //
  ////////////////////////////////////////////////////////////

  function integer get_response_queue_depth();
    return(response_queue_depth);
  endfunction  

endclass
