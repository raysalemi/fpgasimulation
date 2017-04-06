// $Id: test.sv,v 1.5 2008/09/02 09:53:45 jlrose Exp $
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

/*
About: phases/stop_request
This test case will test a hierarchy that contains ovm_components, using ovm_env.

ovm_env calls the global_stop_request


To get detailed information about the ovm_components, ovm_phases and ovm_env.You may check the following files:
	- ovm/src/base/ovm_phases.sv
	- ovm/src/base/ovm_component.sv
	- ovm/src/base/ovm_env.svh
*/






module test;
  import ovm_pkg::*;

  //Create a topology
  //            top
  //       |            |
  //     u1(A)         u2(A)
  //    |            |   
  //   b1(B)       b1(B)  

  //Has run phase
  class B extends ovm_component;
    rand logic [7:0] delay = 50;
    function new (string name, ovm_component parent);
      super.new(name,parent);
    endfunction
    task run();
      $display("%0t: %0s:  start run phase", $time, get_full_name());
      #delay;
      $display("%0t: %0s:  end run phase", $time, get_full_name());
    endtask
    function void report();
      $display("%0t: %0s:  In report phase", $time, get_full_name());
    endfunction
  endclass
  
  //Has run phase and contains subcomponents
  class A extends ovm_component;
    rand B b1;
    rand logic [7:0] delay= 75;

    bit alldone = 0;

    function new (string name, ovm_component parent);
      super.new(name,parent);
      b1 = new("b1", this);
      //Interrupt a stop request to allow to finish processing
      enable_stop_interrupt = 1;
    endfunction
    task run();
      $display("%0t: %0s:  start run phase", $time, get_full_name());
      #delay;
      $display("%0t: %0s:  end run phase", $time, get_full_name());

      //indicate done processing
      alldone = 1;
    endtask

    //do the stop interrupt processing
    task stop(string ph_name);
      $display("%0t: %0s:  In the stop interrupt, waiting for alldone", $time, get_full_name());
      if(!alldone) @(posedge alldone);
      $display("%0t: %0s:  Done with the stop interrupt", $time, get_full_name());
    endtask
  endclass

  //Top level contains two A components
  class top extends ovm_env;
    rand A a1;
    rand A a2;
    function new (string name, ovm_component parent);
      super.new(name,parent);
      a1 = new("a1", this);
      a2 = new("a2", this);
    endfunction
    task run();
      $display("%0t: %0s:  start run phase", $time, get_full_name());
      #75 global_stop_request();
      //can also just use stop_request() on this env
      #1000;  //run the env a long time because when it is done, everything is done
      $display("%0t: %0s:  end run phase", $time, get_full_name());
    endtask
  endclass


  top t = new("top", null);

  initial begin
    //Randomize all of the delays
    void'(t.randomize());

    //run_test and do_test are alternate ways to do phasing. top.do_test only phases
    //this environment, independently of anything else. run_test is a global 
    //mechanism and will phase everything together.
    `ifdef DOTEST
    t.do_test();
    `else
    run_test();
    `endif
  end
endmodule
