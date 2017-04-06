-- *******************************************************************
-- Copyright 2008 Ray Salemi

-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License. 
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.
-- ********************************************************************
--
-- VHDL Architecture all_vhdl_ovl.tb_top_vhdl.tb_top
--
-- Created:
--          by - Ray.UNKNOWN (OFFICE)
--          at - 09:08:15 08/15/2007
--
-- using Mentor Graphics HDL Designer(TM) 2006.1 (Build 72)
--
LIBRARY ieee;
LIBRARY std;
use std.textio.all;
use ieee.std_logic_textio.all;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.STD_LOGIC_UNSIGNED.all; 
LIBRARY work;

ENTITY tb_top IS
END ENTITY tb_top;

--
ARCHITECTURE tb OF tb_top IS  

   SIGNAL clk      : std_logic;
   SIGNAL rst      : std_logic;
   SIGNAL data_out : std_logic_vector( 2 DOWNTO 0 );
   COMPONENT threebitcounter
      PORT (
         clk      : IN     std_logic;
         data_in  : IN     std_logic_vector( 2 DOWNTO 0 );
         inc      : IN     std_logic;
         ld       : IN     std_logic;
         rst      : IN     std_logic;
         data_out : BUFFER std_logic_vector( 2 DOWNTO 0 )
      );
   END COMPONENT;
   FOR ALL : threebitcounter USE ENTITY work.threebitcounter;
BEGIN
   --  hds hds_inst
   DUT : threebitcounter
      PORT MAP (
         clk      => clk,
         data_in  => "000",
         inc      => '1',
         ld       => '0',
         rst      => rst,
         data_out => data_out
      );
      
 -- purpose: Make the clock and reset
 -- type   : combinational
 -- inputs : 
 -- outputs: clk, rst
reseter: process
 begin  -- process clocker
   rst <= '1';
   wait for 20 ns;
   rst <= '0';
   wait;
 end process reseter; 

-- purpose: make the clock go
-- type   : combinational
-- inputs : 
-- outputs: clk
clocker: process
   variable myline : line;
begin  -- process clocker
  clk <= '0';
  while true loop
    wait for 10 ns;
    clk <= not clk;
    write (myline, string'("data_out: "));
    write (myline, data_out);
    writeline(output,myline);
  end loop;
end process clocker;

END ARCHITECTURE tb;

