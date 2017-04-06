// $Id: ovm_phase_defines.svh,v 1.8 2008/07/18 10:15:20 redelman Exp $
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

`ifndef SVPP
`ifndef INCA
`define ovm_phase_type_name_decl(NAME) \
    virtual function string get_type_name (); \
      return `"NAME``_phase #(PARENT)`"; \
    endfunction
`else
`define ovm_phase_type_name_decl(NAME) \
    virtual function string get_type_name (); \
      return `"NAME``_phase`"; \
    endfunction
`endif
`endif

`define ovm_phase_func_decl(NAME,TOP_DOWN) \
  class NAME``_phase #(type PARENT=int) extends ovm_phase; \
    function new(); \
      super.new(`"NAME`",TOP_DOWN,0); \
    endfunction \
    `ovm_phase_type_name_decl(NAME) \
    virtual function void call_func(ovm_component parent); \
      PARENT m_parent; \
      if($cast(m_parent,parent)) \
        m_parent.NAME(); \
    endfunction \
  endclass

  
`define ovm_phase_task_decl(NAME,TOP_DOWN) \
  class NAME``_phase #(type PARENT=int) extends ovm_phase; \
    function new(); \
      super.new(`"NAME`",TOP_DOWN,1); \
    endfunction \
    `ovm_phase_type_name_decl(NAME) \
    virtual task call_task(ovm_component parent); \
      PARENT m_parent; \
      if($cast(m_parent,parent)) \
        m_parent.NAME(); \
    endtask \
  endclass


`define ovm_phase_func_topdown_decl(NAME)  `ovm_phase_func_decl(NAME,1)
`define ovm_phase_func_bottomup_decl(NAME) `ovm_phase_func_decl(NAME,0)
`define ovm_phase_task_topdown_decl(NAME)  `ovm_phase_task_decl(NAME,1)
`define ovm_phase_task_bottomup_decl(NAME) `ovm_phase_task_decl(NAME,0)
  
