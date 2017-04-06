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
-- ********************************************************************--
-- VHDL Entity threebitcounter
--

LIBRARY ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.STD_LOGIC_UNSIGNED.all;


ENTITY threebitcounter IS
   PORT( 
      clk          : IN     std_logic;
      data_in      : IN     std_logic_vector ( 2 DOWNTO 0 );
      inc          : IN     std_logic;
      ld           : IN     std_logic;
      rst          : IN     std_logic;
      data_out     : BUFFER std_logic_vector ( 2 DOWNTO 0 );
      error        : OUT    std_logic
   );

-- Declarations

END threebitcounter ;

--
-- VHDL Architecture threebitcounter.rtl
--
--

ARCHITECTURE rtl OF threebitcounter IS



   component assertion
     port (
       clk          : in  std_logic;
       rst          : in  std_logic;
       inc          : in  std_logic;
       ld           : in  std_logic;
       data_in      : in  std_logic_vector(2 downto 0);
       data_out     : in  std_logic_vector(2 downto 0);
       error        : out std_logic);   -- Assertion error
   end component;


BEGIN

  
  firewall: assertion
    port map (
      clk          => clk,
      rst          => rst,
      inc          => inc,
      ld           => ld,
      data_in      => data_in,
      data_out     => data_out,
      error        => error);
 
  
   -----------------------------------------------------------------
   counter : PROCESS (clk)
   -----------------------------------------------------------------
   BEGIN
      IF (clk'EVENT AND clk = '1') THEN
         IF (rst = '1') THEN
             data_out <= "000" ;
         ELSE
            IF ld = '1' THEN
               data_out <= data_in;
            ELSIF inc = '1' THEN
               data_out <= std_logic_vector(data_out + "001");
            END IF;
         END IF;
      END IF;
   END PROCESS counter;


END rtl;
