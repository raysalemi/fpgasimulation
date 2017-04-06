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
library accellera_ovl_vhdl;
use accellera_ovl_vhdl.std_ovl.all;
use accellera_ovl_vhdl.std_ovl_procs.all;
package proj_pkg is
-- OVL configuration
  constant ovl_proj_controls : ovl_ctrl_record := (
-- generate statement controls
    xcheck_ctrl            =>     OVL_ON,
    implicit_xcheck_ctrl   =>     OVL_ON,
    init_msg_ctrl          =>     OVL_OFF,
    init_count_ctrl        =>     OVL_OFF,
    assert_ctrl            =>     OVL_ON,
    cover_ctrl             =>     OVL_OFF,
    global_reset_ctrl      =>     OVL_OFF,
    finish_ctrl            =>     OVL_ON,
    gating_ctrl            =>     OVL_ON,

-- user configurable library constants
    max_report_error       =>     4,
    max_report_cover_point =>     15,
    runtime_after_fatal    =>    "150 ns    ",

-- default values for common generics
    severity_level_default => OVL_SEVERITY_DEFAULT,
    property_type_default  => OVL_PROPERTY_DEFAULT,
    msg_default            => ovl_set_msg("My Default Message"),
    coverage_level_default => OVL_COVER_DEFAULT,
    clock_edge_default     => OVL_CLOCK_EDGE_DEFAULT,
    reset_polarity_default => OVL_ACTIVE_HIGH,
    gating_type_default    => OVL_GATING_TYPE_DEFAULT
    );
end package proj_pkg;
