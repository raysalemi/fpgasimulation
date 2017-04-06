// $Id: ovm_root.svh,v 1.16 2008/09/03 07:20:10 jlrose Exp $
//------------------------------------------------------------------------------
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
//------------------------------------------------------------------------------

`ifndef OVM_ROOT_SVH
`define OVM_ROOT_SVH

`define OVM_DEFAULT_TIMEOUT 9200s

//------------------------------------------------------------------------------
//
// CLASS: ovm_root (phase controller)
//
//------------------------------------------------------------------------------
// The OVM environment contains a single instance of ovm_root, called ovm_top.
// The ovm_top serves as THE top-level component for all components. A component
// becomes a child of ovm_top when its 'parent' constructor argument is null.
//
// run_test
//   Phases all components through all registered phases. If the optional
//   test_name argument is provided, or if a command-line plusarg, +OVM_TESTNAME,
//   is found, the specified test is created prior to phasing. The test may
//   contain new verification components or the entire testbench, in which case
//   the test and testbench can be chosen from the command line without forcing
//   recompilation. If the global (package) variable, finish_on_completion, is
//   set, $finish is called after phasing completes.
//   
// insert_phase
//   This method is used to register phases with ovm_root. The new phase (1st
//   argument) is inserted _after_ the phase given by the 2nd argument. If the
//   2nd argument is null, the new phase becomes the first phase.
//
// run_global_phase
//   Note: all phasing should be started via run_test. This method is used to
//   run up to and through the phase given by the 1st argument. If null, then
//   all remaining phases will be run, effectively completing simulation.
// 
// stop_request
//   Calling this function triggers the process of shutting down the currently
//   running task-based phase.  This process involves calling all components'
//   stop tasks for those components whose enable_stop_interrupt bit is set.
//   Once all stop tasks return, or once the optional global_stop_timeout
//   expires, all components' kill method is called, effectively ending the
//   current phase. The ovm_top will then begin execution of the next phase,
//   if any.
//
// find / find_all
//    Returns the component handle (find) or list of components handles (find_all)
//    matching a given string. The string may contain the wildcards, * and ?.
//    Strings beginning with '.' are absolute path names. If optional comp arg
//    provided, search begins from that component down (default=all components).
//
// time phase_timeout / stop_timeout
//    These set watchdog timers for task-based phases and stop tasks. Their
//    default value is set to the maximum time. A timeout at this value usually
//    indicates a problem with your testbench. You should lower the timeout to
//    prevent "never-ending" simulations. Setting the value to 0 turns off the
//    timer.
//
// enable_print_topology
//    If set, the topology is printed just after the end_of_elaboration phase.
//
// finish_on_completion
//    If set, run_test will issue a $finish after all phases are executed.
//------------------------------------------------------------------------------


class ovm_root extends ovm_component;

  extern static function ovm_root get();

  extern virtual task   run_test         (string test_name="");

  extern task           run_global_phase (ovm_phase phase=null);      

  extern function void  stop_request     ();

  extern function void  insert_phase     (ovm_phase new_phase,
                                          ovm_phase exist_phase);
  extern function
          ovm_component find             (string comp_match);
  extern function void  find_all         (string comp_match,
                                          ref ovm_component comps[$],
                                          input ovm_component comp=null);

  extern function ovm_phase get_current_phase ();
  extern function ovm_phase get_phase_by_name (string name);

  virtual function string get_type_name(); return "ovm_root"; endfunction

  time phase_timeout = 0;
  time stop_timeout  = 0;
  bit  enable_print_topology = 0;
  bit  finish_on_completion  = 1;


  // PRIVATE members

  extern `_protected function new ();

  extern local task m_do_phase_all (ovm_component comp, ovm_phase phase);
  extern local task m_stop_process ();
  extern local task m_stop_request (time timeout=0);
  extern local task m_do_stop_all  (ovm_component comp);
  extern local function void m_reset_phase(ovm_component comp,
                                           ovm_phase phase=null);

  local  ovm_phase  m_phase_q[ovm_phase];
  local  ovm_phase  m_first_phase = null;
  local  ovm_phase  m_last_phase = null;
  local  event      m_stop_request_e;

  ovm_phase m_curr_phase = null;
  static local ovm_root m_inst;

  /*** DEPRECATED - Do not use in new code.  Convert code when appropriate ***/
  extern function void print_unit_list (ovm_component comp=null);
  extern function void print_unit      (string name, ovm_printer printer=null);
  extern function void print_units     (ovm_printer printer=null);
  extern function void print_topology  (ovm_printer printer=null);

endclass

// ovm_enable_print_topology (global, deprecated)
// -------------------------

bit ovm_enable_print_topology = 0;

// our singleton top-level; it is initialized upon first call to ovm_root::get

`const ovm_root ovm_top = ovm_root::get();


// run_test
// --------

task run_test (string test_name="");
  ovm_root top;
  top = ovm_root::get();
  top.run_test(test_name);
endtask


// global_stop_request 
// -------------------

function void global_stop_request();
  ovm_root top;
  top = ovm_root::get();
  top.stop_request();
endfunction


// set_global_timeout 
// ------------------

function void set_global_timeout(time timeout);
  ovm_root top;
  top = ovm_root::get();
  top.phase_timeout = timeout;
endfunction


// set_global_stop_timeout
// -----------------------

function void set_global_stop_timeout(time timeout);
  ovm_root top;
  top = ovm_root::get();
  top.stop_timeout = timeout;
endfunction


// ovm_find_component (deprecated)
// ------------------

function ovm_component ovm_find_component (string comp_name);
  ovm_root top;
  top = ovm_root::get();
  return top.find(comp_name);
endfunction

  
// ovm_print_topology (deprecated)
// ------------------

function void ovm_print_topology(ovm_printer printer=null);
  ovm_report_handler::ovm_report_deprecated("ovm_print_topology()");
  ovm_top.print_topology(printer);
endfunction



//-----------------------------------------------------------------------------
//
// IMPLEMENTATION
//
//-----------------------------------------------------------------------------

// get
// ---

function ovm_root ovm_root::get();
  if (m_inst == null)
    m_inst = new();
  return m_inst;
endfunction


// new
// ---

function ovm_root::new();
  super.new("__top__", null);
  report_header();
  print_enabled=0;
endfunction



//------------------------------------------------------------------------------
// Primary Simulation Entry Points
//------------------------------------------------------------------------------

ovm_component ovm_test_top; // deprecated; do not use

// run_test
// --------

task ovm_root::run_test(string test_name="");

  ovm_factory factory = ovm_factory::get();
  bit testname_plusarg;
  string msg;

  testname_plusarg = 0;

  // plusarg overrides argument
  if ($value$plusargs("OVM_TESTNAME=%s", test_name))
    testname_plusarg = 1;

  if ($value$plusargs("TESTNAME=%s", test_name)) begin
    ovm_report_warning("DPRFT",
          "+TESTNAME is deprecated. Use +OVM_TESTNAME instead.");
    testname_plusarg = 1;
  end

  // if test now defined, create it using common factory
  if (test_name != "") begin
    if(m_children.exists("ovm_test_top")) begin
      ovm_report_fatal("TTINST",
          "An ovm_test_top already exists via a previous call to run_test");
      #0; // forces shutdown because $finish is forked
    end
    $cast(ovm_test_top, factory.create_component_by_name(test_name,
          "ovm_test_top", "ovm_test_top", null));

    assert_test_not_found : assert(ovm_test_top != null) else begin
      msg = testname_plusarg ? "command line (+OVM_TESTNAME=": "call to run_test(";
      ovm_report_fatal("INVTST",
          {"Requested test from ",msg, test_name, ") not found." });
      $fatal;     
    end
  end

  if (m_children.num() == 0) begin
    ovm_report_fatal("NOCOMP",
          {"No components instantiated. You must instantiate",
           " at least one component before calling run_test. To run",
           " a test, use +OVM_TESTNAME or supply the test name in",
           " the argument to run_test(). Exiting simulation."});
    return;
  end

  ovm_report_info("RNTST", {"Running test ",test_name, "..."}, OVM_LOW);

  fork 
    // isolated from calling process
    run_global_phase();
  join

  report_summarize();

  if (finish_on_completion) begin
    // forking allows current delta to complete
    fork
      $finish;
    join_none
  end

endtask


// m_reset_phase
// -------------

function void ovm_root::m_reset_phase(ovm_component comp, ovm_phase phase=null);
  string name;

  if (comp.get_first_child(name))
    do
      this.m_reset_phase(comp.get_child(name));
    while (comp.get_next_child(name));

  comp.m_curr_phase=phase;

endfunction

//------------------------------------------------------------------------------
// Phase control
//------------------------------------------------------------------------------

// run_global_phase
// ----------------

task ovm_root::run_global_phase(ovm_phase phase=null);

  time timeout;

  if (m_curr_phase != null) begin
    ovm_report_fatal("PHSSTR", "Global phasing has already started."); 
    #0; // forces shutdown because $finish is forked
    return;     
  end

  // If we weren't given a specific phase, run through them all.

  if (phase == null) begin
    phase = m_last_phase;
  end

  if (!m_phase_q.exists(phase)) begin
    ovm_report_fatal("PHNTFD", {"Phase %0s not registered.",phase.get_name()}); 
    return;
  end

  if (m_curr_phase == phase || phase.is_done()) begin
    ovm_report_warning("PHDONE", $psprintf(
       "Phase '%0s' already executed. Current phase is '%0s'.",
       phase.get_name(), m_curr_phase.get_name()));
    return;
  end

  // MAIN LOOP: Executes all phases from the current phase
  // through the phase given in the argument.
  while (m_curr_phase != phase) begin

    if (m_curr_phase == null)
      m_curr_phase = m_first_phase;
    else
      m_curr_phase = m_phase_q[m_curr_phase];

    // Trigger phase's in_progress event.
    // The #0 allows any waiting processes to resume before we continue.
    m_curr_phase.m_set_in_progress();
    #0;

    ovm_report_info("STARTPH",
      $psprintf("STARTING PHASE %0s",m_curr_phase.get_name()),int'(OVM_FULL)+1);

    // TASK-based phase
    if (m_curr_phase.is_task()) begin

      event wait_forever;

      timeout = (phase_timeout==0) ?  `OVM_DEFAULT_TIMEOUT - $time :
                                      phase_timeout;

      `ifdef INCA

        // IUS does not support disabling named fork blocks, so we isolate the
        // inner fork block so we can kill it using disable fork
        fork // guard process
        begin

        fork

          // Start an independent process that kills the phase, else the killing
          // stops prematurely at the component that issued the request.
          m_stop_process();

          begin // guard process
            fork
              begin
                #0; // ensures stop_process active before potential stop_request
                m_do_phase_all(this,m_curr_phase);
                @wait_forever; // wait for stop or timeout
              end
              begin
                #timeout ovm_report_error("TIMOUT",
                      $psprintf("Watchdog timeout of '%0t' expired.", timeout));
              end
            join_any
            disable fork;
          end // end guard process

        join_any
        disable fork;

        end
        join // end guard process

      `else // QUESTA

        fork : task_based_phase
          m_stop_process();
          begin
            m_do_phase_all(this,m_curr_phase);
            wait fork;
          end
          #timeout ovm_report_error("TIMOUT",
                $psprintf("Watchdog timeout of '%0x' expired.", timeout));
        join_any
        disable task_based_phase;

      `endif // INCA-QUESTA

    end // if (is_task)

    // FUNCTION-based phase
    else begin
      m_do_phase_all(this,m_curr_phase);
    end

    ovm_report_info("ENDPH",
      $psprintf("ENDING PHASE %0s",m_curr_phase.get_name()),int'(OVM_FULL)+1);

    // Trigger phase's done event.
    // The #0 allows any waiting processes to resume before we continue.
    m_curr_phase.m_set_done();
    #0;

    // If error occurred during elaboration, exit with FATAL.
    if (m_curr_phase == end_of_elaboration_ph) begin
      ovm_report_server srvr;
      srvr = get_report_server();
      if(srvr.get_severity_count(OVM_ERROR) > 0) begin
        ovm_report_fatal("ovm", "elaboration errors");
        #0; // $finish is called in a forked process in ovm_report_object::die.
            // this forces that process to start, preventing us from continuing
      end

      if (enable_print_topology || ovm_enable_print_topology)
        print_topology();
    end

    // if next phase is end_of_elab, the resolve all connections
    if (m_phase_q[m_curr_phase] == end_of_elaboration_ph)
      do_resolve_bindings();

  end

endtask


// m_do_phase_all
// --------------

task ovm_root::m_do_phase_all (ovm_component comp, ovm_phase phase);

  // run_global_phase calls this private task for each phase in consecutive
  // order.  If the phase is a function, then all components' functions are
  // called sequentially in top-down or bottom-up order. If the phase is a
  // task, all components' do_task_phase tasks are forked and we return
  // with no waiting. The caller can subsequently call 'wait fork' to wait
  // for the forked tasks to complete.

  ovm_phase curr_phase;
  bit done[string];

  curr_phase = comp.m_curr_phase;

  // This while loop is needed in case new componenents are created
  // several phases into a simulation.

  while (curr_phase != phase) begin

    ovm_phase ph;
    done.delete();

    if (curr_phase == null)
      curr_phase = m_first_phase;
    else
      curr_phase = m_phase_q[curr_phase];

    // bottom-up
    if (!curr_phase.is_top_down()) begin
      string name;
      if (comp.get_first_child(name)) begin
        do begin
          m_do_phase_all(comp.get_child(name),curr_phase);
          done[name] = 1;
        end
        while (comp.get_next_child(name));
      end
    end

    ovm_report_info("COMPPH", $psprintf("*** comp %0s (%0s) curr_phase is %0s",
      comp.get_full_name(),comp.get_type_name(),curr_phase.get_name()),int'(OVM_FULL)+1);

    if (curr_phase.is_task()) begin
      // We fork here to ensure that do_task_phase, a user-overridable task,
      // does not inadvertently block this process
      fork
        comp.do_task_phase(curr_phase);
      join_none
    end
    else
      comp.do_func_phase(curr_phase);

    // bottom-up 2nd pass: phase newly created components, if any
    if (!curr_phase.is_top_down()) begin

      while (comp.get_num_children() != done.num()) begin
        string name;
        if (comp.get_first_child(name)) begin
          do begin
            if (!done.exists(name)) begin
              m_do_phase_all(comp.get_child(name),curr_phase);
              done[name] = 1;
            end
          end
          while (comp.get_next_child(name));
        end
      end
    end

    // top-down
    else begin
      string name;
      if (comp.get_first_child(name))
        do begin
          m_do_phase_all(comp.get_child(name),curr_phase);
        end
        while (comp.get_next_child(name));
    end

  end
endtask


// get_current_phase
// -----------------

function ovm_phase ovm_root::get_current_phase();
  return m_curr_phase;
endfunction


//------------------------------------------------------------------------------
// Stopping
//------------------------------------------------------------------------------

// stop_request
// ------------

function void ovm_root::stop_request();
  ->m_stop_request_e;
endfunction


// m_stop_process
// --------------

task ovm_root::m_stop_process();
  @m_stop_request_e;
  m_stop_request(stop_timeout);
endtask


// m_stop_request
// --------------

task ovm_root::m_stop_request(time timeout=0);

  if (timeout == 0)
    timeout = `OVM_DEFAULT_TIMEOUT - $time;

  // stop request valid for running task-based phases only
  if (m_curr_phase == null || !m_curr_phase.is_task()) begin
    ovm_report_warning("STPNA",
      $psprintf("Stop-request has no effect outside non-time-consuming phases",
                "current phase is ",m_curr_phase==null?
                "none (not started":m_curr_phase.get_name()));
    return;
  end

  // All stop tasks are forked from a single thread so 'wait fork'
  // can be used. We fork the single thread as well so that 'wait fork'
  // does not wait for threads previously started by the caller's thread.

  // IUS does not support disabling named fork blocks, so we isolate the
  // inner fork block so we can kill it using disable fork
  `ifdef INCA

  fork begin // guard process
    fork
      begin
        m_do_stop_all(this);
        wait fork;
      end
      begin
        #timeout ovm_report_warning("STPTO",
         $psprintf("Stop-request timeout of %0t expired. Stopping phase '%0s'",
                           timeout, m_curr_phase.get_name()));
      end
    join_any
    disable fork;
  end
  join

  `else // QUESTA

  fork : stop_tasks
    begin
      m_do_stop_all(this);
      wait fork;
    end
    begin
      #timeout ovm_report_warning("STPTO",
       $psprintf("Stop-request timeout of %0t expired. Stopping phase '%0s'",
                         timeout, m_curr_phase.get_name()));
    end
  join_any
  disable stop_tasks;

  `endif // INCA

  // all stop processes have completed, or a timeout has occured
  this.do_kill_all();

endtask


// m_do_stop_all
// -------------

task ovm_root::m_do_stop_all(ovm_component comp);

  string name;

  // we use an external traversal to ensure all forks are 
  // made from a single threaad.
  if (comp.get_first_child(name))
    do begin
      m_do_stop_all(comp.get_child(name));
    end
    while (comp.get_next_child(name));

  if (comp.enable_stop_interrupt) begin
    fork begin
      comp.stop(m_curr_phase.get_name());
    end
    join_none
  end

endtask


//------------------------------------------------------------------------------
// Phase Insertion
//------------------------------------------------------------------------------

// insert_phase
// ------------

function void ovm_root::insert_phase(ovm_phase new_phase,
                                     ovm_phase exist_phase);
  ovm_phase exist_ph;
  string s;

  if (build_ph.is_done()) begin
    ovm_report_fatal("PHINST", "Phase insertion after build phase prohibited.");
    return;
  end

  if (exist_phase != null && exist_phase.is_done() ||
      exist_phase == null && m_curr_phase != null) begin 
    ovm_report_fatal("PHINST", {"Can not insert a phase at a point that has ",
      "already executed. Current phase is '", m_curr_phase.get_name(),"'."});
    return;
  end

  if (new_phase == null) begin
    ovm_report_fatal("PHNULL", "Phase argument is null.");
    return;
  end

  if (exist_phase != null && !m_phase_q.exists(exist_phase)) begin
    ovm_report_fatal("PHNTFD", {"Phase '",exist_phase.get_name(),
                      "' is not registered."});
    return;
  end

  if (m_phase_q.exists(new_phase)) begin
    if ((exist_phase == null && m_first_phase != new_phase) ||
        (exist_phase != null && m_phase_q[exist_phase] != new_phase)) begin
      ovm_report_error("PHDUPL", {"Phase '", new_phase.get_name(),
        "' is already registered in a different order."});
    end
    return;
  end

  if (exist_phase == null) begin
    m_phase_q[new_phase] = m_first_phase;
    m_first_phase = new_phase;
  end
  else begin
    m_phase_q[new_phase] = m_phase_q[exist_phase];
    m_phase_q[exist_phase] = new_phase;
  end

  if (m_phase_q[new_phase] == null)
    m_last_phase = new_phase;

endfunction


// get_phase_by_name
// -----------------

function ovm_phase ovm_root::get_phase_by_name (string name);
  ovm_phase m_ph;
  foreach (m_phase_q[ph]) begin
    m_ph = ph;
    if(m_ph.get_name() == name) 
      return ph;
  end
  return null;
endfunction


//------------------------------------------------------------------------------
// Component Search & Printing
//------------------------------------------------------------------------------


// find_all
// --------

function void ovm_root::find_all(string comp_match, ref ovm_component comps[$],
                                 input ovm_component comp=null); 
  string name;
  `ifdef INCA
  static ovm_component tmp[$]; //static list to work around ius 6.2 limitation
  static bit s_is_child;  //starts at 0 for the root call
         bit is_child;    //automatic variable gets updated immediately on entry
  is_child = s_is_child;
  `endif

  if (comp==null)
    comp = this;

  if (comp.get_first_child(name))
    do begin
      `ifdef INCA
        //Indicate that a recursive call is being made. Using a static variable
        //since this is a temp workaround and we don't want to effect the
        //function prototype.
        s_is_child = 1;
        this.find_all(comp_match,tmp,comp.get_child(name));
        s_is_child = 0;  //reset for a future call.
        //Only copy to the component list if this is the top of the stack,
        //otherwise an infinite loop will result copying tmp to itself.
        if(is_child==0)
          while(tmp.size()) comps.push_back(tmp.pop_front());
      `else
        this.find_all(comp_match,comps,comp.get_child(name));
      `endif
    end
    while (comp.get_next_child(name));

  if (ovm_is_match(comp_match, comp.get_full_name()) &&
       comp.get_name() != "") /* ovm_top */
    comps.push_back(comp);

endfunction


// find
// ----

function ovm_component ovm_root::find (string comp_match);
  `ifdef INCA
    static ovm_component comp_list[$];
    comp_list.delete();
  `else
    ovm_component comp_list[$];
  `endif

  find_all(comp_match,comp_list);

  if (comp_list.size() > 1)
    ovm_report_warning("MMATCH",
    $psprintf("Found %0d components matching '%s'. Returning first match, %0s.",
              comp_list.size(),comp_match,comp_list[0].get_full_name()));

  if (comp_list.size() == 0)
    ovm_report_warning("CMPNFD",
      {"Component matching '",comp_match,"' was not found in the list of ovm_components"});
  return comp_list[0];
endfunction


//------------------------------------------------------------------------------
//
// REVIEW FOR DEPRECATION OR REMOVAL
//
//------------------------------------------------------------------------------

// print_unit
// ----------

function void ovm_root::print_unit (string name, ovm_printer printer=null);

  ovm_component comp;
  comp = find(name);
  if (comp)
    comp.print(printer);
endfunction


// print_units
// -----------

function void ovm_root::print_units (ovm_printer printer=null);

  // Can replace implementation with one line, which will produce single table
  //   this.print(printer);

  string s;

  if (m_children.num()==0) begin
    ovm_report_warning("EMTCOMP", "No OVM components to print.");
    return;
  end

  if (printer==null)
    printer = ovm_default_printer;

  if (printer.knobs.sprint)
    s = printer.m_string;

  foreach (m_children[c]) begin
    if(m_children[c].print_enabled) begin
      printer.print_object("", m_children[c]);  
      if(printer.knobs.sprint)
        s = {s, printer.m_string};
    end
  end

  printer.m_string = s;


endfunction


// print_unit_list
// ---------------

function void ovm_root::print_unit_list(ovm_component comp=null);

  string name;

  if (comp==null) begin
    comp = this;
    if (m_children.num()==0) begin
      ovm_report_warning("NOUNIT","No OVM components to print. ");
      return;
    end
    $display("List of ovm components");
  end
  else begin
    $display("%s (%s)", comp.get_full_name(), comp.get_type_name());
  end

  if (comp.get_first_child(name))
    do begin
      this.print_unit_list(comp.get_child(name));
    end
    while (comp.get_next_child(name));

endfunction


// print_topology
// --------------

function void ovm_root::print_topology(ovm_printer printer=null);
  ovm_report_info("OVMTOP", "OVM testbench topology:", OVM_LOW);
  print_units(printer);
endfunction


`endif //OVM_ROOT_SVH
