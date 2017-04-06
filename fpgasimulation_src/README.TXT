/*************************************************************************
   Copyright 2008 Ray Salemi

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
**************************************************************************/

      FPGA Simulation: A Complete Step-by-Step Guide Source Code

			    by Ray Salemi


VERSION 1.0

Welcome to the source file repository for "FPGA Simulation: A Complete
Step-by-Step Guide".  This directory contains all the source code
examples from the book.

When I wrote FPGA Simulation, I wanted to make sure that all the code
examples worked. There is nothing more frustrating than errors in
teaching examples, because the new learners cannot tell the difference
between errors and concepts they don't understand yet.

To avoid syntax errors, I compiled and simulated every example in the
book.  Then I captured screen shots of the code and used them as
figures.  This kept the spell-checker from mangling the code.  The
result was, I hope, error-free examples.

LICENSING

All the code in these examples is licensed under the Apache License
agreement. This agreement gives you wide latitude to use the code in
your own work.  See the link for details.

DIRECTORY ORGANIZATION

This directory contains all the source code used in the book.  All the
files compile and simulate in Questa 6.4c, but they can work with
versions as early as 6.3.  

The directory is organized by chapters and sections.  The directory
names match section numbers in the book, so you can easily find the
actual code for any code example.

Each directory contains all the code to run the example, except for
three common directories.  All examples assume that these common
directories are two directory levels above the example.  So it is best
to copy the entire directory structure when sharing an example.

SHARED DIRECTORIES

The three shared directories contain libraries that are common to all
examples.  They are under the top-level directory, fpgaSim.  The three
common directories are

* ovm---This is OVM V2.0, released August 5, 2008.  You can replace this
  directory with later versions of OVM if you like, but it still needs
  to be named "ovm".

* std_ovl---This is the Open Verification Library V2.3, released June
  6, 2008.  You can replace this version with later versions of the
  OVL.  The OVL ships with a std_ovl directory, simply replace this
  one with the new one.

* tinyalu_common---The TinyALU is a VHDL design that we verify
  completely in the book.  All its source files are here.  There are
  also SystemVerilog package files that contain transaction
  definitions.

RUNNING THE EXAMPLES

All the examples contain a Tcl script called run.do.  This script runs
with ModelSim or Questa.  You can run any example by CDing to the
directory with the example and typing the following command:

% vsim -do run.do  

Or, if you don't want the GUI, type this:

% vsim -c -do run.do

Or, from within ModelSim or Questa

VSIM> do run.do

In all cases, the simulator will create the work library, compile the
example, and run the design.

ERRATA

Please report any errors in these files to errata@fpgasimulation.com.
I will update these files and notify users through the
fpgasimulation.com email newsletter.

Thanks!

Ray Salemi
