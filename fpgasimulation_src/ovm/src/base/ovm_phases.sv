// $Id: ovm_phases.sv,v 1.9 2008/08/22 11:39:53 redelman Exp $
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

`ifndef OVM_PHASES_SVH
`define OVM_PHASES_SVH

typedef class ovm_component;

//------------------------------------------------------------------------------
//
// Class: ovm_phase
//
//------------------------------------------------------------------------------
// This class is a base class for a phase callback. All predefined OVM phases
// and any user-defined phases alike use ovm_phase. To define a new phase:
//
// (1)  derive a subclass of ovm_phase that implements (overrides) either the
//      call_task  or call_func method, depending on whether the new phase is
//      to be time-consuming or not.  When calling super.new, your subclass must
//      provide the name of phase (typically the name of the callback method),
//      whether the method is to be called top-down or bottom-up, and whether
//      the method is task or a function. For example, given a component type,
//      my_comp, you can define a my_task phase for that component as follows:
//
//        class my_comp extends ovm_component;
//          ...
//          virtual my_task();  return; endtask // make virtual
//          ...
//        endclass
//
//        class my_task_phase extends ovm_phase;
//          function new();
//            super.new("my_task",1,1);
//          endfunction
//          task call_task(ovm_component parent);
//             my_comp_type my_comp;
//             if ($cast(my_comp,parent))
//               my_comp.my_task_phase()
//          endtask
//        endclass
//      
//      Tip: The above can be defined via a convenient macro invocation:
//
//           `ovm_phase_task_topdown_decl(my_task)
//
// (2)  Create a global (or package-scope) instance of your phase object:
//
//        my_task_phase my_task_ph = new();
//
// (3)  Register the phase with the OVM's phase controller, ovm_top. For
//      example, to register the my_task_phase as a phase for all my_comp-
//      based components:
//        
//        ovm_top.insert_phase(my_task_ph, run_ph);
//
//      It should be global in nature so that it is universally available 
//      to any process for getting or waiting on phase state.
//
// That's it! The ovm_top phase controller will now call my_comp-based components'
// my_task phase callbacks in top-down order after completion of the run phase.
//
//
// Type information methods:
//
//   The methods get_name, is_task, and is_top_down provide information about
//   the phase's type.
// 
// Event & status methods:
//
//   The ovm_phase class defines an event interface that allows processes to
//   wait until the phase begins or ends and to determine whether the phase is
//   currently active (is_in_progress) or has completed (is_done). The reset
//   method clears the phase state.
//
//------------------------------------------------------------------------------


virtual class ovm_phase;

  local  string  m_name;
  local  bit     m_is_top_down;
  local  bit     m_is_task;

  local  event   m_start_event;
  local  bit     m_is_started=0;
  local  event   m_done_event;
  local  bit     m_is_done=0;

  function new (string name, bit is_top_down, bit is_task);
    m_name = name;
    m_is_top_down = is_top_down;
    m_is_task     = is_task;
  endfunction

  //
  // Info interface
  //
  function string get_name       (); return m_name;        endfunction
  function bit    is_task        (); return m_is_task;     endfunction
  function bit    is_top_down    (); return m_is_top_down; endfunction

  virtual function string get_type_name();
    return "ovm_phase";
  endfunction

  //
  // Event & Status interface
  //
  task            wait_start     (); @m_start_event;       endtask
  task            wait_done      (); @m_done_event;        endtask

  function bit    is_in_progress (); return m_is_started;  endfunction
  function bit    is_done        (); return m_is_done;     endfunction

  function void   reset          (); m_is_done=0;
                                     m_is_started=0;       endfunction

  //
  // Virtual methods call_task/call_func: subclasses must define only one
  //
  virtual task call_task (ovm_component parent);
     return;
  endtask

  virtual function void call_func (ovm_component parent);
    return;
  endfunction

  // psuedo-private methods; do not call directly

  function void m_set_is_started(bit val);
    m_is_started=val;
  endfunction

  function void m_set_in_progress();
    m_set_is_started(1);
    ->m_start_event;
  endfunction

  function void m_set_done();
    m_is_done=1;
    m_set_is_started(0);
    ->m_done_event;
  endfunction

endclass


`endif // OVM_PHASES_SVH
