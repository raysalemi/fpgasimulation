// $Id: component.sv,v 1.8 2008/09/02 09:53:45 jlrose Exp $
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

package pkg;

import ovm_pkg::*;

class my_component extends ovm_component;

  function new(string name, ovm_component parent);
    super.new(name, parent);
  endfunction

  task run();
    ovm_report_info("component", "hello out there!");
  endtask

endclass

endpackage

module test;
   import ovm_pkg::*;
   import pkg::*;
   my_component t;
   
   initial begin
      t = new("Top", null);
   end
endmodule // test

