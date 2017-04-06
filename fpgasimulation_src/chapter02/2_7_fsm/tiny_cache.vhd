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
-- VHDL Entity tinycache_sv_lib.tiny_cache_vhd.symbol
--
-- File   : tiny_cache_vhd_fsm.vhd
--
-- Created:
--          by - user.group
--          at - 13:03:34 14 May 2007
--
-- Mentor Graphics' HDL Designer(TM)
--
-- Description:
-- Entity description for VHDL version of the Tinycache

LIBRARY ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;

USE work.cache_vhd_pkg.all;

ENTITY tiny_cache_vhd IS
   PORT( 
      clk         : IN     std_logic;
      cpu_address : IN     address_t;
      cpu_rd      : IN     std_logic;
      cpu_wr      : IN     std_logic;
      rst         : IN     std_logic;
      cpuwait     : OUT    std_logic;
      mem_address : OUT    address_t;
      mem_rd      : OUT    std_logic;
      mem_wr      : OUT    std_logic;
      cpu_data    : INOUT  data_t;
      mem_data    : INOUT  data_t
   );

END tiny_cache_vhd ;

--
-- VHDL Architecture tinycache_sv_lib.tiny_cache_vhd.fsm
--
-- File   : tiny_cache_vhd_fsm.vhd
--
-- Created:
--          by - user.group
--          at - 13:03:34 14 May 2007
--
-- Mentor Graphics' HDL Designer(TM)
--
-- Description:
-- VHDL version of the Tinycache

LIBRARY ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;

USE work.cache_vhd_pkg.all;
 
ARCHITECTURE fsm OF tiny_cache_vhd IS

   -- Architecture Declarations
   SIGNAL cache_address : std_logic_vector( 3 DOWNTO 0 );  
   SIGNAL cache_ram     : cache_ram_t;  
   SIGNAL key_ram       : key_ram_t;  
   SIGNAL invalid       : std_logic_vector( cache_depth DOWNTO 0 );  
   SIGNAL cpuwait_int   : std_logic;  
   SIGNAL mem_wr_int    : std_logic;  

   TYPE STATE_TYPE IS (
      RESET,
      HIT,
      WRITE,
      MISS
   );
 
   -- Declare current and next state signals
   SIGNAL current_state : STATE_TYPE;
   SIGNAL next_state : STATE_TYPE;

BEGIN

   -----------------------------------------------------------------
   clocked_proc : PROCESS ( 
      clk
   )
   -----------------------------------------------------------------
   BEGIN
      IF (clk'EVENT AND clk = '1') THEN
         IF (rst = '1') THEN
            current_state <= RESET;
         ELSE
            current_state <= next_state;

            -- Combined Actions
            CASE current_state IS
               WHEN RESET => 
                  invalid <= (others => '1');
               WHEN WRITE => 
                  key_ram(conv_integer(unsigned(cache_address)))   <= cpu_address;
                  invalid(conv_integer(unsigned(cache_address)))   <= '0';
                  cache_ram(conv_integer(unsigned(cache_address))) <= cpu_data;
               WHEN MISS => 
                  key_ram(conv_integer(unsigned(cache_address)))   <= cpu_address;
                  invalid(conv_integer(unsigned(cache_address)))   <= '0';
                  cache_ram(conv_integer(unsigned(cache_address))) <= mem_data;
               WHEN OTHERS =>
                  NULL;
            END CASE;
         END IF;
      END IF;
   END PROCESS clocked_proc;
 
   -----------------------------------------------------------------
   nextstate_proc : PROCESS ( 
      cpu_wr,
      cpuwait_int,
      current_state
   )
   -----------------------------------------------------------------
   BEGIN
      CASE current_state IS
         WHEN RESET => 
            next_state <= HIT;
         WHEN HIT => 
            IF (cpuwait_int = '1') THEN 
               next_state <= MISS;
            ELSIF (cpu_wr = '1') THEN 
               next_state <= WRITE;
            ELSE
               next_state <= HIT;
            END IF;
         WHEN WRITE => 
            next_state <= HIT;
         WHEN MISS => 
            next_state <= HIT;
         WHEN OTHERS =>
            next_state <= RESET;
      END CASE;
   END PROCESS nextstate_proc;
 
   -----------------------------------------------------------------
   output_proc : PROCESS ( 
      current_state
   )
   -----------------------------------------------------------------
   BEGIN
      -- Default Assignment
      mem_rd <= '0';
      mem_wr_int <= '0';

      -- Combined Actions
      CASE current_state IS
         WHEN HIT => 
            mem_wr_int <= '0';
         WHEN WRITE => 
            mem_wr_int <= '1';
         WHEN MISS => 
            mem_rd <= '1';
         WHEN OTHERS =>
            NULL;
      END CASE;
   END PROCESS output_proc;
 
   -- Concurrent Statements
   cpu_data      <= cache_ram(conv_integer(unsigned(cache_address))) WHEN cpu_rd = '1' ELSE (others => 'Z');
   mem_data      <= cpu_data WHEN mem_wr_int = '1' ELSE (others => 'Z');
   cache_address <= cpu_address(3 downto 0);
   mem_address   <= cpu_address;
   cpuwait_int   <= '1' WHEN
      (((key_ram(conv_integer(unsigned(cache_address))) /= cpu_address) 
      OR (invalid(conv_integer(unsigned(cache_address))) = '1')) 
      AND (cpu_rd = '1'))
   ELSE '0';
   cpuwait       <= cpuwait_int;
   mem_wr        <= mem_wr_int;
   
END fsm;
