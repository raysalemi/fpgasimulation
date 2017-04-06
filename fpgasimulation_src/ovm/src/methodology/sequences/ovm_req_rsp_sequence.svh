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
/******************************************************************************

  FILE : ovm_req_rsp_sequence.svh
                                                                                
******************************************************************************/

`ifndef OVM_REQ_RSP_SEQUENCE_SVH
`define OVM_REQ_RSP_SEQUENCE_SVH


//-----------------------------------------------------------------------------
//
// CLASS: ovm_req_rsp_sequence
//
//-----------------------------------------------------------------------------

class ovm_req_rsp_sequence #(type REQ = ovm_sequence_item,
       type RSP = ovm_sequence_item) extends ovm_sequence;

  function new(string name = "ovm_req_rsp_sequence",
    ovm_sequencer_base sequencer=null,
    ovm_sequence parent_seq=null);
    super.new(name, sequencer, parent_seq);
  endfunction

  task apply(input REQ this_req, output RSP this_rsp);
    ovm_sequence_item item;
    super.apply(this_req, item);
    $cast(this_rsp, item);
  endtask

endclass
 

`endif // OVM_REQ_RSP_SEQUENCE_SVH
