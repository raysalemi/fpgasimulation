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
-- ********************************************************************-- *******************************************************************
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
-- VHDL Package Header tinycache_sv.cache_vhd_pkg
--
-- File   : tiny_cache.sv
--
-- Created:
--          by - user.group
--          at - 13:03:34 26 Mar 2007
--
-- Mentor Graphics' HDL Designer(TM)
--
-- Description:
-- Types and constants for VHDL version of Tinycache RTL
--

LIBRARY ieee;
USE ieee.std_logic_1164.all;

PACKAGE cache_vhd_pkg IS
  
  CONSTANT CACHE_ADDRESS_WIDTH  : integer := 8;
  CONSTANT MEMORY_ADDRESS_WIDTH : integer := 8;
  CONSTANT DATA_WIDTH           : integer := 8;
  CONSTANT CACHE_DEPTH          : integer := (2**CACHE_ADDRESS_WIDTH)-1;
  CONSTANT MEMORY_DEPTH         : integer := (2**MEMORY_ADDRESS_WIDTH)-1;
  
  SUBTYPE data_t          IS std_logic_vector (DATA_WIDTH-1 downto 0);
  SUBTYPE address_t       IS std_logic_vector (MEMORY_ADDRESS_WIDTH-1 downto 0);
  SUBTYPE cache_address_t IS std_logic_vector (CACHE_ADDRESS_WIDTH-1 downto 0);
  
  TYPE cache_ram_t        IS ARRAY (CACHE_DEPTH DOWNTO 0) OF std_logic_vector(DATA_WIDTH-1 DOWNTO 0);
  TYPE key_ram_t          IS ARRAY (CACHE_DEPTH DOWNTO 0) OF address_t;

END cache_vhd_pkg;
