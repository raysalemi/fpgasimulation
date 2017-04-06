// $Id: tlm_ifs.svh,v 1.8 2008/08/25 14:48:29 redelman Exp $
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

//----------------------------------------------------------------------
//
// TLM Interfaces
//
//----------------------------------------------------------------------
//
// The unidirectional TLM interfaces are divided into put, get and peek
// interfaces, and blocking, nonblocking and combined interfaces.
// 
// A blocking call always succeeds, but may need to consume time to do
// so. As a result, these methods must be tasks.
//
// A nonblocking call may not succeed, but consumes no time. As a result,
// these methods are functions.
//
// The difference between get and peek is that get consumes the data
// while peek does not. So successive calls to peek with no calls get
// or try_get are guaranteed to return the same value.
//
// The transport interface is a bidirectional blocking interface used
// when the request and response are tightly coupled in a one to one
// relationship.
//----------------------------------------------------------------------

`define TASK_ERROR "TLM interface task not implemented"
`define FUNCTION_ERROR "TLM interface function not implemented"

virtual class tlm_if_base #(type T1=int, type T2=int);

  virtual task put( input T1 t );
    ovm_report_error("put", `TASK_ERROR);
  endtask

  virtual task get( output T2 t );
    ovm_report_error("get", `TASK_ERROR);
  endtask

  virtual task peek( output T2 t );
    ovm_report_error("peek", `TASK_ERROR);
  endtask

  virtual function bit try_put( input T1 t );
    ovm_report_error("try_put", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit can_put();
    ovm_report_error("can_put", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit try_get( output T2 t );
    ovm_report_error("try_get", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit can_get();
    ovm_report_error("can_get", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit try_peek( output T2 t );
    ovm_report_error("try_peek", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit can_peek();
    ovm_report_error("can_ppeek", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual task transport( input T1 req , output T2 rsp );
    ovm_report_error("transport", `TASK_ERROR);
  endtask

  virtual function bit nb_transport(input T1 req, output T2 rsp);
    ovm_report_error("nb_transport", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function void write( input T1 t );
    ovm_report_error("write", `FUNCTION_ERROR);
  endfunction

endclass

// primtive interfaces
`define TLM_BLOCKING_PUT_MASK          (1<<0)
`define TLM_BLOCKING_GET_MASK          (1<<1)
`define TLM_BLOCKING_PEEK_MASK         (1<<2)
`define TLM_BLOCKING_TRANSPORT_MASK    (1<<3)

`define TLM_NONBLOCKING_PUT_MASK       (1<<4)
`define TLM_NONBLOCKING_GET_MASK       (1<<5)
`define TLM_NONBLOCKING_PEEK_MASK      (1<<6)
`define TLM_NONBLOCKING_TRANSPORT_MASK (1<<7)

`define TLM_ANALYSIS_MASK              (1<<8)

// combination interfaces
`define TLM_PUT_MASK                  (`TLM_BLOCKING_PUT_MASK    | `TLM_NONBLOCKING_PUT_MASK)
`define TLM_GET_MASK                  (`TLM_BLOCKING_GET_MASK    | `TLM_NONBLOCKING_GET_MASK)
`define TLM_PEEK_MASK                 (`TLM_BLOCKING_PEEK_MASK   | `TLM_NONBLOCKING_PEEK_MASK)

`define TLM_BLOCKING_GET_PEEK_MASK    (`TLM_BLOCKING_GET_MASK    | `TLM_BLOCKING_PEEK_MASK)
`define TLM_BLOCKING_MASTER_MASK      (`TLM_BLOCKING_PUT_MASK       | `TLM_BLOCKING_GET_MASK | `TLM_BLOCKING_PEEK_MASK)
`define TLM_BLOCKING_SLAVE_MASK       (`TLM_BLOCKING_PUT_MASK       | `TLM_BLOCKING_GET_MASK | `TLM_BLOCKING_PEEK_MASK)

`define TLM_NONBLOCKING_GET_PEEK_MASK (`TLM_NONBLOCKING_GET_MASK | `TLM_NONBLOCKING_GET_MASK)
`define TLM_NONBLOCKING_MASTER_MASK   (`TLM_NONBLOCKING_PUT_MASK    | `TLM_NONBLOCKING_GET_MASK | `TLM_NONBLOCKING_PEEK_MASK)
`define TLM_NONBLOCKING_SLAVE_MASK    (`TLM_NONBLOCKING_PUT_MASK    | `TLM_NONBLOCKING_GET_MASK | `TLM_NONBLOCKING_PEEK_MASK)

`define TLM_GET_PEEK_MASK             (`TLM_GET_MASK | `TLM_PEEK_MASK)
`define TLM_MASTER_MASK               (`TLM_BLOCKING_MASTER_MASK    | `TLM_NONBLOCKING_MASTER_MASK)
`define TLM_SLAVE_MASK                (`TLM_BLOCKING_MASTER_MASK    | `TLM_NONBLOCKING_MASTER_MASK)
`define TLM_TRANSPORT_MASK            (`TLM_BLOCKING_TRANSPORT_MASK | `TLM_NONBLOCKING_TRANSPORT_MASK)

