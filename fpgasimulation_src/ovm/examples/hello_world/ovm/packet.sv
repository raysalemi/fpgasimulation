// $Id: packet.sv,v 1.3 2007/12/14 10:18:56 redelman Exp $
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

class packet extends ovm_transaction;

`ifndef NO_RAND
  rand
`endif
  int addr;

  `ovm_object_utils_begin(packet)
    `ovm_field_int(addr, OVM_ALL_ON)
  `ovm_object_utils_end

  constraint c { addr >= 0 && addr < 'h100; }

endclass

