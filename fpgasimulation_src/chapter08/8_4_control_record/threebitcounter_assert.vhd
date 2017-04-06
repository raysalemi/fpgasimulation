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
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
library accellera_ovl_vhdl;
use accellera_ovl_vhdl.std_ovl.all;
use accellera_ovl_vhdl.std_ovl_components.all;

use work.my_ovl_control_pkg.all;

entity threebitcounter_assert is
                        
  port (
    clk          : in  std_logic;
    rst          : in  std_logic;
    inc          : in  std_logic;
    ld           : in  std_logic;
    data_in      : in  std_logic_vector(2 downto 0);
    data_out     : in  std_logic_vector(2 downto 0)
    );        
  
end threebitcounter_assert;


architecture RTL of threebitcounter_assert is

  signal overflow : std_logic;          
  signal fire :     std_logic_vector(OVL_FIRE_WIDTH-1 downto 0);
  signal enable:    std_logic;

begin  -- RTL

  overflow <= '1' when ((data_out = "111") and (inc = '1')) else '0';
  enable   <= '1' when (rst = '0') else '1';

  u_counter_overflow: ovl_never
    generic map (
      reset_polarity => OVL_ACTIVE_HIGH,
      controls       => my_ovl_controls)
    port map (
      clock     => clk,
      reset     => rst,
      enable    => enable,
      test_expr => overflow,
      fire      => fire);

end RTL;
  
