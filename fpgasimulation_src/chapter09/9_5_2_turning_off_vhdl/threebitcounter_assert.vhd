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
use ieee.std_logic_unsigned.all;
library accellera_ovl_vhdl;
use accellera_ovl_vhdl.std_ovl.all;
use accellera_ovl_vhdl.std_ovl_components.all;
use work.proj_pkg.all;

entity threebitcounter_assert is
                        
  port (
    clk          : in  std_logic;
    rst          : in  std_logic;
    inc          : in  std_logic;
    ld           : in  std_logic;
    data_in      : in  std_logic_vector(2 downto 0);
    data_out     : in  std_logic_vector(2 downto 0);
    error        : out std_logic);        
  
end threebitcounter_assert;


architecture RTL of threebitcounter_assert is

  signal overflow : std_logic;          -- capture the overflow condition
  signal fire : std_logic_vector(OVL_FIRE_WIDTH-1 downto 0);  -- assertion signals

  COMPONENT ovl_never
    GENERIC (
      msg            : string             := OVL_MSG_NOT_SET;
      controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS;
      reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET
      );
    PORT (
      clock     : IN     std_logic;
      reset     : IN     std_logic;
      enable    : IN     std_logic;
      test_expr : IN     std_logic;
      fire      : OUT    std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
      );
   end COMPONENT;

begin  -- RTL

  overflow <= '1' when ((data_out = "111") and (inc = '1')) else '0';

  error <= fire(OVL_FIRE_2STATE);
  
  cntr_overflow: ovl_never
    generic map (
      reset_polarity => OVL_ACTIVE_HIGH,
      controls       => ovl_proj_controls)
    port map (
      clock     => clk,
      reset     => rst,
      enable    => '1',
      test_expr => overflow,
      fire      => fire);

end RTL;
  
