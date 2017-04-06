/*
About: do_test
this test will test running two run phases in parallel.



Walk through the test:
create a thread *A* with a run task which has a delay of 55 ns.

create an env class *myenv* with a run task which has a dealy of 10 ns.

when the top module call do_test, the test will terminate after the first 10 ns , because the run() in the env myenv is element that controls the test when using do_test. When myenv::run terminates then the entire test shuts down.

*/


package user_pkg;

import ovm_pkg::*;


//----------------------------------------------------------------------
// A
//----------------------------------------------------------------------
class A extends ovm_component;
  function new(string name, ovm_component parent);
    super.new(name, parent);
  endfunction
  task run;
    $display("%0t: Hi from %s   top %0s", $time, get_full_name(),
            m_parent.get_full_name());
    #55;
    $display("%0t: Done from %s", $time, get_full_name());
  endtask
endclass

//----------------------------------------------------------------------
// myenv
//----------------------------------------------------------------------
class myenv extends ovm_env;
  A aa;
  function new(string name, ovm_component parent=null);
    super.new(name, parent);
    aa = new("a", this);
  endfunction

  task run;
    $display("%0t: Hi from %s", $time, get_full_name());
    #10;
    $display("%0t: Done from %s", $time, get_full_name());
  endtask
endclass

endpackage:user_pkg

//----------------------------------------------------------------------
// top
//----------------------------------------------------------------------
module top;
  import user_pkg::*;
  myenv env = new("env");
  initial env.do_test();
endmodule
