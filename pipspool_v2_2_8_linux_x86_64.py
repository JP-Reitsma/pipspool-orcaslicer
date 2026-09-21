# /// script
# dependencies = []
# [tool.orcaslicer.plugin]
# name = "PipSpool"
# description = "Spoolman synchronization plugin for OrcaSlicer"
# author = "Donko"
# version = "2.2.8"
# ///

"""PipSpool: synchronize Spoolman inventory into OrcaSlicer presets.

This implementation intentionally has no slicing-pipeline capability. Klipper
and Moonraker remain responsible for real-time Spoolman usage accounting.
"""

from __future__ import annotations

import json
import math
import os
import re
import sys
import threading
import base64
import time
import webbrowser
from dataclasses import dataclass, field
from html import escape
from pathlib import Path
from typing import Any

import orca


# Ask once, during plugin loading, for the bundled IDNA files Python may read
# before its HTTP connection audit event. Orca persists explicitly requested
# filesystem permissions in the plugin install state across normal restarts.
_python_lib = Path(os.__file__).parent
_idna_source = _python_lib / "encodings" / "idna.py"
_idna_bytecode = (
    _python_lib
    / "encodings"
    / "__pycache__"
    / f"idna.{sys.implementation.cache_tag}.pyc"
)
orca.request_permissions(
    fs_read=[str(_idna_source), str(_idna_bytecode)]
)

# If Orca's bundled IDNA bytecode is stale, Python normally writes a temporary
# ``.pyc.<random>`` file before replacing it. That path changes every launch
# and therefore cannot be remembered by Orca's permission store. Preload IDNA
# without writing bytecode, then restore the interpreter setting immediately.
_original_dont_write_bytecode = sys.dont_write_bytecode
try:
    sys.dont_write_bytecode = True
    import encodings.idna
    import http.client
    import urllib.parse
finally:
    sys.dont_write_bytecode = _original_dont_write_bytecode


# Public default. Configure the Spoolman server address in PipSpool Settings.
DEFAULT_SPOOLMAN_URL = "http://localhost:7912"
DEFAULT_LOW_STOCK_THRESHOLD_GRAMS = 100.0
PLUGIN_VERSION = "2.2.8"
COPYRIGHT_YEAR = 2026
FEEDBACK_URL = "https://github.com/Gadonk/pipspool-orcaslicer/issues"
LATEST_RELEASE_API = "https://api.github.com/repos/Gadonk/pipspool-orcaslicer/releases/latest"
UPDATE_CHECK_INTERVAL_SECONDS = 6 * 60 * 60
SETTINGS_FILENAME = "pipspool_settings.json"
LOG_FILENAME = "pipspool.log"
SPOOLMAN_CONNECTION_MESSAGE = (
    "Connection to the Spoolman server was lost or could not be established. "
    "Check that Spoolman is running, then select Refresh."
)

# Requests/urllib3 reaches Python's targetless ``socket.__new__`` audit event,
# while urllib may load IDNA codecs before Orca approves the URL. http.client
# emits ``http.client.connect`` with the target host before either operation,
# allowing Orca to persist the grant and suppress the nested audit events.
class _HttpResponse:
    def __init__(self, url: str, status_code: int, body: bytes):
        self.url = url
        self.status_code = status_code
        self._body = body

    def raise_for_status(self) -> None:
        if 200 <= self.status_code < 400:
            return
        detail = self._body.decode("utf-8", errors="replace").strip()
        if len(detail) > 240:
            detail = detail[:237] + "..."
        suffix = f": {detail}" if detail else ""
        raise RuntimeError(f"HTTP {self.status_code} for {self.url}{suffix}")

    def json(self) -> Any:
        return json.loads(self._body.decode("utf-8"))


class _HttpSession:
    def request(
        self,
        method: str,
        url: str,
        *,
        params: dict[str, Any] | None = None,
        json: Any = None,
        headers: dict[str, str] | None = None,
        timeout: float = 10,
    ) -> _HttpResponse:
        if params:
            separator = "&" if urllib.parse.urlsplit(url).query else "?"
            url = f"{url}{separator}{urllib.parse.urlencode(params)}"
        request_headers = dict(headers or {})
        data = None
        if json is not None:
            data = globals()["json"].dumps(json).encode("utf-8")
            request_headers.setdefault("Content-Type", "application/json")
        request_headers.setdefault("Accept", "application/json")
        parsed = urllib.parse.urlsplit(url)
        if parsed.scheme not in {"http", "https"} or not parsed.hostname:
            raise ValueError(f"Unsupported HTTP URL: {url}")
        port = parsed.port or (443 if parsed.scheme == "https" else 80)
        path = urllib.parse.urlunsplit(("", "", parsed.path or "/", parsed.query, ""))
        connection_type = (
            http.client.HTTPSConnection
            if parsed.scheme == "https"
            else http.client.HTTPConnection
        )
        connection = connection_type(parsed.hostname, port, timeout=timeout)
        try:
            connection.request(method.upper(), path, body=data, headers=request_headers)
            response = connection.getresponse()
            return _HttpResponse(url, int(response.status), response.read())
        finally:
            connection.close()

    def get(self, url: str, **kwargs) -> _HttpResponse:
        return self.request("GET", url, **kwargs)

    def post(self, url: str, **kwargs) -> _HttpResponse:
        return self.request("POST", url, **kwargs)

    def patch(self, url: str, **kwargs) -> _HttpResponse:
        return self.request("PATCH", url, **kwargs)

    def delete(self, url: str, **kwargs) -> _HttpResponse:
        return self.request("DELETE", url, **kwargs)


HTTP_SESSION = _HttpSession()
PROFILE_SUFFIX = " - PipSpool.json"
START_MARKER = "; PipSpool: begin managed spool ID"
END_MARKER = "; PipSpool: end managed spool ID"
LEGACY_START_MARKER = "; Spoolman Bridge: begin managed spool ID"
LEGACY_END_MARKER = "; Spoolman Bridge: end managed spool ID"
ORCA_FIELD_PREFIX = "orca_"
# These belong to OrcaSlicer's Dependencies tab. PipSpool never infers them;
# they are synchronized only when the user explicitly selects those fields.
ORCA_DEPENDENCY_KEYS = (
    "compatible_printers",
    "compatible_printers_condition",
    "compatible_prints",
    "compatible_prints_condition",
)
ORCA_SETTING_GROUPS = {
    "Filament": (
        "filament_density", "filament_diameter", "filament_cost",
        "filament_max_volumetric_speed", "filament_flow_ratio",
        "filament_shrink", "filament_shrinkage_compensation_z",
        "nozzle_temperature", "nozzle_temperature_initial_layer",
        "hot_plate_temp", "hot_plate_temp_initial_layer",
        "textured_plate_temp", "textured_plate_temp_initial_layer",
        "cool_plate_temp", "cool_plate_temp_initial_layer",
        "textured_cool_plate_temp", "textured_cool_plate_temp_initial_layer",
        "eng_plate_temp", "eng_plate_temp_initial_layer",
        "supertack_plate_temp", "supertack_plate_temp_initial_layer",
    ),
    "Cooling": (
        "close_fan_the_first_x_layers", "full_fan_speed_layer",
        "fan_min_speed", "fan_cooling_layer_time", "fan_max_speed",
        "slow_down_layer_time", "reduce_fan_stop_start_freq",
        "slow_down_for_layer_cooling", "dont_slow_down_outer_wall",
        "slow_down_min_speed", "enable_overhang_bridge_fan",
        "overhang_fan_threshold", "overhang_fan_speed",
        "internal_bridge_fan_speed", "support_material_interface_fan_speed",
        "ironing_fan_speed", "additional_cooling_fan_speed",
        "activate_air_filtration", "activate_air_filtration_during_print",
        "during_print_exhaust_fan_speed", "activate_air_filtration_on_completion",
        "complete_print_exhaust_fan_speed",
    ),
    "Setting Overrides": (
        "filament_retraction_length", "filament_z_hop",
        "filament_z_hop_types", "filament_retract_lift_above",
        "filament_retract_lift_below", "filament_retract_lift_enforce",
        "filament_retraction_speed", "filament_deretraction_speed",
        "filament_retract_restart_extra",
        "filament_retraction_minimum_travel",
        "filament_retract_when_changing_layer", "filament_wipe",
        "filament_wipe_distance", "filament_retract_before_wipe",
        "filament_retract_after_wipe", "filament_long_retractions_when_cut",
        "filament_retraction_distances_when_cut",
        "filament_retract_length_toolchange",
        "filament_retract_restart_extra_toolchange",
        "filament_ironing_flow", "filament_ironing_spacing",
        "filament_ironing_inset", "filament_ironing_speed",
    ),
    "Advanced": (
        "filament_start_gcode", "filament_change_extrusion_role_gcode",
        "filament_end_gcode",
    ),
    "Multimaterial": (
        "filament_minimal_purge_on_wipe_tower",
        "filament_tower_interface_pre_extrusion_dist",
        "filament_tower_interface_pre_extrusion_length",
        "filament_tower_ironing_area", "filament_tower_interface_purge_volume",
        "filament_tower_interface_print_temp", "long_retractions_when_ec",
        "retraction_distances_when_ec", "filament_loading_speed_start",
        "filament_loading_speed", "filament_unloading_speed_start",
        "filament_unloading_speed", "filament_toolchange_delay",
        "filament_cooling_moves", "filament_cooling_initial_speed",
        "filament_cooling_final_speed", "filament_stamping_loading_speed",
        "filament_stamping_distance", "filament_ramming_parameters",
        "filament_multitool_ramming", "filament_multitool_ramming_volume",
        "filament_multitool_ramming_flow", "filament_change_length",
    ),
    "Dependencies": ORCA_DEPENDENCY_KEYS,
    "Notes": ("filament_notes",),
}
ORCA_SETTINGS = tuple(
    setting for settings in ORCA_SETTING_GROUPS.values() for setting in settings
)
ORCA_SETTING_UNITS = {
    "filament_density": "g/cm³",
    "filament_diameter": "mm",
    "filament_cost": "currency/kg",
    "filament_max_volumetric_speed": "mm³/s",
    "filament_shrink": "%",
    "filament_shrinkage_compensation_z": "%",
    "nozzle_temperature": "°C",
    "nozzle_temperature_initial_layer": "°C",
    "hot_plate_temp": "°C",
    "hot_plate_temp_initial_layer": "°C",
    "textured_plate_temp": "°C",
    "textured_plate_temp_initial_layer": "°C",
    "cool_plate_temp": "°C",
    "cool_plate_temp_initial_layer": "°C",
    "textured_cool_plate_temp": "°C",
    "textured_cool_plate_temp_initial_layer": "°C",
    "eng_plate_temp": "°C",
    "eng_plate_temp_initial_layer": "°C",
    "supertack_plate_temp": "°C",
    "supertack_plate_temp_initial_layer": "°C",
    "fan_min_speed": "%",
    "fan_max_speed": "%",
    "overhang_fan_threshold": "%",
    "overhang_fan_speed": "%",
    "internal_bridge_fan_speed": "%",
    "support_material_interface_fan_speed": "%",
    "ironing_fan_speed": "%",
    "additional_cooling_fan_speed": "%",
    "during_print_exhaust_fan_speed": "%",
    "complete_print_exhaust_fan_speed": "%",
    "fan_cooling_layer_time": "s",
    "slow_down_layer_time": "s",
    "slow_down_min_speed": "mm/s",
    "filament_minimal_purge_on_wipe_tower": "mm³",
    "filament_tower_interface_pre_extrusion_dist": "mm",
    "filament_tower_interface_pre_extrusion_length": "mm",
    "filament_tower_ironing_area": "mm²",
    "filament_tower_interface_purge_volume": "mm³",
    "filament_tower_interface_print_temp": "°C",
    "retraction_distances_when_ec": "mm",
    "filament_loading_speed_start": "mm/s",
    "filament_loading_speed": "mm/s",
    "filament_unloading_speed_start": "mm/s",
    "filament_unloading_speed": "mm/s",
    "filament_toolchange_delay": "s",
    "filament_cooling_initial_speed": "mm/s",
    "filament_cooling_final_speed": "mm/s",
    "filament_stamping_loading_speed": "mm/s",
    "filament_stamping_distance": "mm",
    "filament_multitool_ramming_volume": "mm³",
    "filament_multitool_ramming_flow": "mm³/s",
    "filament_change_length": "mm",
    "filament_retraction_length": "mm",
    "filament_z_hop": "mm",
    "filament_retract_lift_above": "mm",
    "filament_retract_lift_below": "mm",
    "filament_retraction_speed": "mm/s",
    "filament_deretraction_speed": "mm/s",
    "filament_retract_restart_extra": "mm",
    "filament_retraction_minimum_travel": "mm",
    "filament_wipe_distance": "mm",
    "filament_retract_before_wipe": "%",
    "filament_retract_after_wipe": "%",
    "filament_retraction_distances_when_cut": "mm",
    "filament_retract_length_toolchange": "mm",
    "filament_retract_restart_extra_toolchange": "mm",
    "filament_ironing_flow": "%",
    "filament_ironing_spacing": "mm",
    "filament_ironing_inset": "mm",
    "filament_ironing_speed": "mm/s",
}
ORCA_INTEGER_SETTINGS = {
    "nozzle_temperature", "nozzle_temperature_initial_layer",
    "hot_plate_temp", "hot_plate_temp_initial_layer",
    "textured_plate_temp", "textured_plate_temp_initial_layer",
    "cool_plate_temp", "cool_plate_temp_initial_layer",
    "textured_cool_plate_temp", "textured_cool_plate_temp_initial_layer",
    "eng_plate_temp", "eng_plate_temp_initial_layer",
    "supertack_plate_temp", "supertack_plate_temp_initial_layer",
    "close_fan_the_first_x_layers", "full_fan_speed_layer",
    "overhang_fan_speed", "internal_bridge_fan_speed",
    "support_material_interface_fan_speed", "ironing_fan_speed",
    "additional_cooling_fan_speed", "during_print_exhaust_fan_speed",
    "complete_print_exhaust_fan_speed", "filament_tower_interface_print_temp",
    "filament_cooling_moves",
}
ORCA_BOOLEAN_SETTINGS = {
    "reduce_fan_stop_start_freq", "slow_down_for_layer_cooling",
    "dont_slow_down_outer_wall", "enable_overhang_bridge_fan",
    "activate_air_filtration", "activate_air_filtration_during_print",
    "activate_air_filtration_on_completion", "long_retractions_when_ec",
    "filament_multitool_ramming",
    "filament_retract_lift_enforce", "filament_retract_when_changing_layer",
    "filament_wipe", "filament_long_retractions_when_cut",
}
ORCA_CHOICE_SETTINGS = {
    "overhang_fan_threshold": ("0%", "10%", "25%", "50%", "75%", "95%"),
}
ORCA_TEXT_SETTINGS = {
    "filament_z_hop_types", "filament_start_gcode",
    "filament_change_extrusion_role_gcode", "filament_end_gcode",
    "compatible_printers", "compatible_printers_condition",
    "compatible_prints", "compatible_prints_condition", "filament_notes",
}
ORCA_LIST_TEXT_SETTINGS = {
    "compatible_printers", "compatible_prints",
}
ORCA_SCALAR_TEXT_SETTINGS = {
    "compatible_printers_condition", "compatible_prints_condition",
}


def orca_setting_field_type(setting: str) -> str:
    """Translate Orca's official config type to the closest Spoolman field."""
    if setting in ORCA_INTEGER_SETTINGS:
        return "integer"
    if setting in ORCA_BOOLEAN_SETTINGS:
        return "boolean"
    if setting in ORCA_CHOICE_SETTINGS:
        return "choice"
    if setting == "filament_ramming_parameters" or setting in ORCA_TEXT_SETTINGS:
        return "text"
    return "float"
FIELD_CONFIG_VERSION = 1
SPOOL_TABLE_COLUMNS = (
    "filament",
    "manufacturer",
    "colour",
    "nozzle",
    "bed",
    "remaining",
    "location",
    "loaded",
    "sync",
)
DEFAULT_SPOOL_TABLE_COLUMNS = (
    "filament", "manufacturer", "colour", "nozzle", "bed", "remaining",
)
SPOOL_TABLE_COLUMN_LABELS = {
    "filament": "Filament",
    "manufacturer": "Manufacturer",
    "colour": "Colour",
    "nozzle": "Nozzle",
    "bed": "Bed",
    "remaining": "Remaining",
    "location": "Location",
    "loaded": "Gate/Toolhead",
    "sync": "Profile status",
}
PIPSPOOL_LOGO_DATA_URI = (
    "data:image/webp;base64,"
    "UklGRsokAABXRUJQVlA4WAoAAAAQAAAAnwAAnwAAQUxQSL4IAAABDAdtI0lSzB/29jy7dwAiYgL6j3BimXHooFEpmm02YmtspCvLdjfmoS5AR5Vno0Kb0F+2hm2bIUnW+8UXg7Vt27Zt27Zt27Zt27Ztczx7TXd8EfH+6O5KVFb/O9eJiAlwG0lu2PTfsuV7BBRBgHjlETEB+N/wIiL9F1EVAHBeXX9EPACMNfEEAwBAvEo/Q4HxN73slW//+u2zZ87bajoAcN5J/2EA9PAf2eLI185aeyIAUHX9AvGY4TXSzGJK0YKR5O+PHLCQByBepdMpsNGfDCm3mCxEkvnzqzadHgDUu06mGHAVablwMsskR7184rLjAIBX6VCKCV9hSLnUFIOR5Pd37D2fAHDeSecRjPUOu3OFyUIiGT+6cM2JAcCrdBiHO9idq45mJPn7ffvNrwCcd9I5FBsz5DqmGCLJ+NElG0wOAKrSGQT6CWMtVp5HERzy+P6LDgDgvJPmU2zCmOvM/xdJ8tMrN5gcALxrvntptVqThUzyn4cOnF8BdY0mmGIIU+16Rosk08enzgP4JvPYkZbbNVnIZPe100IbzOGRkpDEQkfPGDL/WQ/aWA7TjWAqZb0j5xTIreGbymNPWi6TpZizzJhtcWhDOTzcGmzOaVE2fiiQRhJMNZwpB23Fxi2hjeSxCy0nEWjKQ3CN5PBUa4MT/54EYshhupFMpQFFlOScF4Uz5LE3LZfNWlMcuQrUkMPjFemq1ZpIMO1IppYgowxVpBKXbyKPHWm5Ejb0JXbNDudCnHrvREQH4pECAALesgAl6cjvxoLME6feC1qdeDhTofVMQt3G++AwWZx6FfQ6eOYV97/svudefe6uwy5nzK1JEqgdXiC3C3y7iHoV9DrO7Kvue8lz345miym35UawSwxzwrWHU/ScYJ51Dr3ulR+62GsMwSyaBcuVAwVUGF+GoC0VmGTNo2547Rdjr9GCxZRrXAJoo8z10HYQhzlu+JO9xhAsplz/ii0oHcMB0PqJYK//yBjMYq5hFDUCqcS8IFztHM5hDinnnMnqYkPWhPdd7uZt0Lp57MPulHutw7431i/xtwkg9XKYcUSKuc8a1RVAoFT33HD1UlzJkNubqyKqdJgY5oV3TuojmHIIU5tlKUIqARUMmQo9xbuaKDaj5QZQkQAOjA9j4AwLzzcRAHW18DiXoQEkRQRLKIy87dzPR6bw+8vHzAr4Oiju4eNByrCCnEkyk+Toa6aDSnWCF5sjW00KMeWULJBDdoCTqgT+C/5TUQFeWkyBPB6uukn/JqnSCbWNgYdCK3KYvau6Y8BGTsZlodUolmPS3exwkI0fKqRpG9plEnJq3BTa4nEIww3kvAZeC990YV/QgDHjLxNAqnC4l/ZCi/Nk3ARaheDlPtSFqxx4bSWCAV8yvmmBsmqYF/kOqhRM/jfT5rUJDCX+OQmkPIc5uov0YqprNrjyFKsw5iRc5zHNX822tBZQu6XEMTNU4XEkQwsfnWx1DChPcVnni/xjFmhpDvfTOkmUZOOnY0HKErzWWaq7eQV8SYKxvmGsDziJVDKuAi1r0r+Y6mM88mMPKcVhzpBrQH858FD4UhSr0nJ/MOYfx4GU4bF1PyEb94Mv53CGlvDFyiI/cShTcVkBAaZqGLk2tJQHaY3ENgi8thTB64ytfXjkVwMghQRjfd1vyDkuDFfCFEOY2gsjgQfAF3KYP+Wac+TUeAe0kGIdxiJ0OY/8UCBFPHZlKPLhiUOnKuPkTkcm57woXBHFNR2PjHFjaBGHJ2htR4IB5AL3hy8CvMXYdu8IYNxJhQRjfd8oGnh0fgnTjGCqiGvk4QpoAYcFYnV8ypWFFKsz5qrhGsEACVKXwhfahVaZLhKMUOrsQh4nMFR3Mxp3TCHF9bQmGUnKuHshwTMdL29cG1oAeJex/5CyzQvXmsB90q/gnxNBWgPwegtxBeuwEPkGCivuovUx3EPg1dBiOzeFR+NO8EUE4/7OyH5CYpgbrggUuzOkfkLkh4ISHc6nxXYLE4Hnw5cgwJmkDcFM4orQEiDAyh/zmVHIqMjPFVIGRIHbaU3A3N6BJ8CjeADG/YXWAG0YqZRHzwRXFjxWjbQy2HT5wNugKN9jgzEMsaOluEQl8FjqGzJaKsLvMN4LRaUeYx/6NcnYWgdNacy8cNVAgbGWP2wUQ1vF9gm8AB5Viwcwz1tMsX0iq2A1kT+MB6kMEB0AdxYZUptEfsBUQXQk4zrwqKcCS7/PbGWklFJMMZUXu/ijv42hNLUEXgSPuoqHP3kMo6WWkoXMPktL5F9LYoJvaaV1Gt9QSG0ABea8m8zBUi/JAsk05Neffvzxl2+/7yOlGFNqIaVPjpsAY2OB4bTaGX+cBIo6iweWf8RIJrOYSY5+cI9Fpppo/PEmHGuypxlzjiGx12Qhpl7y2wcuOBDAGomxZsah88Oj5s4Bcx/1wlCSzH89ve+M6HPQy7ScIsmRv3/3/d9d7BlDzDmT/OScVSfGon8xtsAFgUMWgUf91QGYeskNNl1zoUkBOO9ExONqdudIvnPUsjNOONbYk8+5wp6XvjWCZApmIZP86b6tdvo7pb4uDPxzIXi0pfOC3p136OkwV3fMiX9sitanXe+iTzJJCxYiyREjmWsbje/MAI+2FVVVJ+jT4wBaTL/NBvHqRESceg8AutCRz40mGYOFQOa6pkBeNxAejelxegrGXTAIrTv1ADDjtrf9TjIFSzWJgfx5M0DRnIot2JW6poYUACDOOwATb3DlVyQZQ0wVpRgyOfTkCaCCBhXgAfIiOJTrVAEMXvywJ/8lyRgsphJSimYhkuQ7B0wNeDSrAGuvBUhJAEQVAKZc5/w3hrFnthDMLMYYzUIIkb2PfvWUJQB4QdMKAAgqFecdAEyzxmG3v/83i8chX71207HrzQQAXtDAoooainoBAJls0Y0POPuGh5576733337t8ZvP2Xe9+SYbjJ7iHTq8qFe0KIIWRb069BPFqVd1AgDiVL06EfRLRfB/9wJWUDgg5hsAAPBZAJ0BKqAAoAA+PRiJQyIhoRgL1eggA8SzBDgAzFHAvS/z3mRV5+6/239Oflr8rukXqjybebv+z90Xzi/zPqg/Rn+Y9wf9Uv9V+uPtafsz7o/3H9Qn6//t77xf+19WP9m+2b5BP6p/p+s89Ar9m/Td/bP4Sf6t/zP2z9pz//+wB/8/UA4QD+Adon9L/IP+S+hv458w/ePy1/sXtg/3ffM6Q8yP459yPyv9p/dn1+/13hP8jv7L1CPx3+Z/4P80P7x+6vuQ7Obbv8F/rv7Z7BHsx9G/y/+E/eT/B+kp/neh31u/zvuA/qh/pfzZ9ZT9XvJa8d/2fuCfzX+1f9D+zfl79NH89/3/85/oP3A9wH6H/gv+x/jv81/5/oK/l39S/2P94/xv/g/zX/6/7n3je0H9tfZ1/WxRP2+fc5ZdvyfuC1yUCcfP9hBKMhmVla+xAfqDHTGRbjCK76TDH99Xfb4EBScNp4luhIrvhEskvQU9dlCT2VZ+yIr8kVA24kvX+AKFzSiNkHFuR2kq6tI+CumwrvgLs+XEpuwMqeJD6w3apfvWq7jdzejda5fECFdNnd4pq4ehEfKgpzzPu9+iCOInePEd2E9EAk29kH3sJHwAlhAnqdpgP0UtTuST1cexXe4/frbzDCmSQ3REyTj3K9A69zmqhuswsEY0v+HhVkgRi76E3c2L8I9E4uXx4/K2793T6YJGGRQhqccg1ImWjLtA5BWFKEWs7AMG5k2zO4HWeiaRhQw/rvvZk+4tRy4FrysxOHsXVexUUhwds4EH1XPZQ+THGcRMQpUB6jNDaBKDQyEa95T6ss5GNIaXItHtyNdpi/bR4828HtgKatbsdsyEEfj1LbN4FkqW2nN/gP7Zl9Kama6qC7dbpq0ElZexdnxNsNlKSjt2PHXlyF/JKzkECBqbjC5jx9LpN/+N9doJumAGMAnxmx+3DWGWRq3Hq52FMQiEi5hAAP7wE4Gy0lFgyj5tQo/FRPorWSJ9b4jN4B0YRgvNQl2nB/skB/odGT9/JUY6SbM+DEzLVSbsKQiZppmn0QGIAoOrql6ib76ilKQ1tUHyFz9/L60gWQ4+vv+Qxyg1lYg4OlJq7meB57fNZ0P1w7HRUVXQrJy17gs0+6FhLRip3P5IzZpwx/MSY2S/QBSUwBUT+y03+VhEbpj61i7clW/v0qs3O46drmxU10SBPqaBrl5tbzGRYekPbhy4nYhRJJxvC7UShXGKsk5oD+LkpeqB4ePyQVg57HR/8PwDRalAx/D/gJ8sioqRM2fjLjcCAzjnrykcjAOuXnme+Wr1rSFhQi6oTta86d6dx/k4p8B5o3v4iCh5+nNzfVHf+FDncbXbBe5oFOIJz2o6AnECzXS11LxE7imrJbUqdnyGIImh7BHGVNHBuqfFQ2R71xWisEcwSaEmBOFF4P9LEnMel6LoqygQlBm27Ms4rih0MDIhn6/JL3VQ5zltEsxiRIXS2fV4JYe159OhC3FuRhJ7kw0rW2/SisyQ0XNHXgXtL9tBoMZklqbLMNlxZ7b+WkNM/DX95TOZmNB7zkhUdLdzqBBd/zM98kvfx5Lx9FFDaVt60PUsViZ9EHUXWt7jqtah1q9mxQLboIsZcjYjwyueDIdUaZ9xQWeaPpwjhNq5bMsHecQUc0ccCCTdksAa3E+7hRBljvEvsC7Ev42jQhUttt8KXem2q9tyt0fCbjFYTdRXS3xI6kHceS6jO/4nyCZv1NVITtjh/IGH3OQOwNz+v3ChRv0P6Z9Jt2m+SB60o+9hYX1gXMhTEZed2s0oLGYH44zx2R0fxFFB0RauOoovtcEyn+P5/RwqpGY8oR3dMpy2HMZb9VxYIvoshSsJMO2pZbgndMyCCWrctp7Z//rpG6klSZm5aYcC2C/aZ3obu9nIXEjAeWdwPxgVWdOevlxN/p+AOwrwNp055d6TMpm0lF7m79/r5gEfUhtYdUJM6H88kY8ldRP0kRDS7l2SAeXjGivN8DcbPcqutRHKHy6SKvefeBnrKqHpKVI7ofK/nAqdH4gq0XAQYvuv6sfF5t9/c4S128GWvyZc4EsF22lxQNLhLzv3lehGWQ2qgngmCUb7UpN99uzFKbfEOn95T0A+0mOTh/q7aqVQL18zMruQBUeW5X67eBU9a4iMZL957qPnNKrXH0tU7gAHMBHYBgDDClhNwCxiGSF4I4ctvwTOU9bI8rN+M1u92ROg6L6CFAifoKMJ44w0cG+TLLE8Ak8S7PJzkdhJMrQW0sAYAPIPCjwr0PXBtjamiKCmMsGPxexb1FkMO2AN3q8PhL/OLM5dKGD6JupkRqGpu5f/bT/VoEIzoqoxf3xJkz2l329DuGucofyp48qOi5T0bYTebFCAgMo6/O1jumJA2BKE1ng0XOSXqRjBzouwTpxn2hIiW8UfDaS0O6t4c0dSikDzUE9GDPuriHFfycN0W5cRHJJyuzTgbadjaKhKDPm39NdULyzlUl+5pKprS+y9GGPF0YaBHgg3P4ebdXnRj5z7vFYl1SuDffLzXGP3yQFJ1m25p8UPTsXoUd/yBQUbWpGN0WNSD2o/JiXm33+1aUn9PGL9PNtEmrzWnwPwZps+rmPojvw64ggBp39fSdIi5tW8gI2VnL1ZpL1K99mavHcbfsTkqj/6JT2TddzrwDrIHQAy3Ise624bSLnHaBsiocDOoOAUVLEhaEd76PVqcYHE9f2mAO4Jq7uWNLLn3Qe4dyrQNyquUf9LlDfHSL9Bn5UXWHbWo5wHzYeuEuUEuDCrSbLm1nV0Mw7i9uCJV1/ScTbdkm5+NjbXrrjUISpGEAivkk1CGb5SN2SQhj5MWJ7Jwnq071kk4YlPRwqVgpSrP85wG4aY7DEyPOwQ/wM4/dFXNHoq652yVK1U2pwiq56FlUoo8oVd8t51uk0xRheny1ic1qrv5t/7kyNhLfjDJRfCyHKLttn6eTXetP8a/6PVYGdngwzYWspb90Zb2nfG+fiO3+mBARBPtaoDpcbZJmPHe659hlGR0j2S3/weG9vrRIurKiiqJ6ygLi+aw+e8ScCWEhBoUPKMr4dmL+9eY4HpVFY18eAYnBFklSiynvaNVeYJlJlY1hPrH8hx5VJ1ZCYPbzgHyVT3f99j4vFLzKh8diDvb9ZN4ZMO8Gmntq9vKxy+go8hVJmuVFbU7HC9GZh1/QyRUMz9flQWmjQ1qp3YVtCXchpXb9bFmS0OY72HYaIErgcMXRhBNYvZdRneJTj52u9iM5n4EBKNgEoOznRamKTm78BXMHIFv1BgDZh8oIPlsxl5FmxtoxQWAnHcjj91QgobcKZfWsMm+TRyPpekxP0NiDQYhTAw6DhLz4YxgTtJHAr5bsPyHfsX4wt1y5dY4wIXJu3r2X8cmpl/KpFaUbqC9+TpVXK0cwAxfoPK2VPHx8hD7ld506DKswPL+Zzv9JDm/FWaqZScu2bfadZF9hPbVBcKfWL0PqwujJ0Osi/AiYxiokl4QSbKJ9/yWS10RH2PyrvUf9WTNfvMrHWZ+SSFh9CL+tF2JluAphDc2nXGv6+i4oII1KtciPBmjcNKWpzbVyZLhI359tj2xHz6D4gUSRLMM6LgmOBHGATjwoHl9+AwODFnl0zLYAi4Gf8HfNU0pr9EPTXcrTyLWAB5awLT06G10Y3iq6wxyEzst3R4Egp72miIX0CpupRFMSVEsqTPpdXFLOPDW3n+SOOg14mYiRfw4NPf9aW+6rviPd7ybK9n1mr44i70kUkjE9J6/7ae6Jk4zn+u168uJXtQRbTm0P59i/Zeon/bNkjr6F6CEQ26m6+Sdg4AyXJI4/Cn6P4XrUBRAs/D/Tjxes3t1p75XiCFc3SjI02n2KehPjkgcRB4RCyPQS5p9cYLC4CYNMAeualtQwNV4XZ0gRn3AJ3sg1iu5uzgHvi/ByGpB/F7+DIv+o244/zHFGlliTRDfTZqYuRJV073g3P+/UNpTZFQ0NC4/1vdeMPxs5yYgl+F3M2zSvpH5xqYbyookRBroLyK6X+dSaz7s/HFK3eL2sESp/Tc209GhR/HLAYhTO+oX6lpeRP61swT5tReXkkiJjyLwprXcy5r7T6EYUYY7W4NpsoaRM44WtQnSvXzXPlko4pb43tlmNi8K8Q36JYjQ0cHE6ozkBjRLCj2JMxszK6UqSdfECSVLzjZTWSEhq2d4hY19gZuBBzUyM3XGXTdIIZEn6BoObtPRuxHeewSCgNuiMlsR/WN3DYxJMyvZbn/ALk8AxhnOzyJOHIJwQdoLAUy9C6MWSICLXDsbGRhRlNfK+XdBrRNkPRL8jC8UE3rRXTxn5QOj7r0Dv7NaccjF+LOGoqulv5o00UEOdxfqwKJ/l+rxVuYbmYikQnyIu76AepnSS9BBmOS+qzb2OFzyrOtwoi4GWkmmi9slUpjV2b3QpwvHAFxXVDFYPSOUZw0Lb5HXiqkNE7iy4P/V3L1/ZRoqNd3CGydvBXmFKD85IxlC4Z0HUUBsG582gAlaSbgNi9IRbHSmpWIInWvEFNqk7+GkAfHlG7rc00u/QpLJJfOT5xdnRgraY9CQhMmxWYPo+zS0iiJD6lOo3UJ2zkiRZ0OykWw8go23MIhQDgms7TLqdr1Vid8SnX8JzMzoWcx5aVf9ZK6/oaEDe/USp6cfMzCClvPol/h6CEOLu1kEk8iGLtrgI65wjceF785SaeaB5M0wIzsBwAPxjQnqXtKwu7ROFT1QSDF9xhYWfYd9MDO/0hnmnjaCj1+1h5Aoy2WfP/ytQuICQPbIXBXXHO4fMZpzGyWHsavNuOlq1RnGADAVZfMFxbXNAGIQDHpgDGgnrwKGj1TPXjnygqxFpYesJuNedeoZBgc0SpbLav0EJpTAIsrouHitOcLPNIY5lPuXToAUrG4ACOKAbhEQZYcNaWlF/2oHorrAvz+hcUi3SFucC9TZUh10DzMpTqCou+Nkuu67bgJ0QaW/1rdSF7Q+JldRUSjJ8I20G3BXc6gh5FuFICmh6JCR/lkBO+93viQWs22jIG4uQuP2lcwBGQFFEE3yXhU86Zx2AamPtxvxv8ufECeOfk2pyA0NUEIlT2VVx1jr536D+JiCSExRDxlOvPyuVCOprQAFKMj3VmnqKdE6be4XG8mGbpJXsa/+PjcYw2Arj+gWClRO1s/eWKabsWoXP/qnAcWWHXKhQtorvXrtTx+hSeiXt/szfOaelgRMfEhTmap1Sgz1njphLPOHBXgBAtxTzWCbJw9z2KIS9i+GL7B5mb0eghtXGRuMt1+ua6C1Y8otSXTNA+caZOzV9n3m9zweWzLisMd8zG83XbElL9EJfa3vJGp9Tj4dOsQAKAH92znBPANh7a1seBq/1c+EayceqbasE0Uj5+fUvKBOXMFU1AIwHlzJhf6G98fWeuRh9Yk5hFNGecGCBAE8cIfo0az5+VYsYxdsGueIjiw8BL4D76K5u4j0XX53lcSFQ0NFD8nswV6WpzhtnheLhd7h7lv1WIHnxQd8tDttFtSt4jwpu5L2WNtmure/fgA9rjw1ZcgvTT5fODAQQKaebiXpO0IhVcuVM3L0ZpkMTKvmpC1Nr2fPwNDh8q+Zy8a72qTCd530OMpUGOlknxDE8EWVrCq5zpPWiWap3IjAZ4OY56FWMtvVvkG0jIbI7CGBCyjI9nvLdEEa0IBI9H5GleggAUPEVeRvWYUkZkSTjH/cQu2KiJD5/nlWohmggfkW3XUNHVskQpFdzWLlSBQpsSPLg7nZRW+uQS9E/5bmrdJrPtN6TCToEYNbT3GA7rOqOTFUPuJ5o5078qgBoLFQYjcHPEJm9NvR3c/Kq2IE9g1ZbAJ2/wa+SV4PsYw/Hb58HfGGZGfw4ZfFLdbDzIfaykHw1BK+xFxEeW2y12Co/8RX+E74ECjaHLQH3IMt8AJhJD0yuiShSSFor1b8c2C8wSk7t7PhBAdYReP5esUhpv8442wOxGebJeYCjlUdGa9z6Mw+PBttW3HJgc7HYzE5THLKhcaUGxcKlU8ByVFeB++I6kNA2ru3J3qjwNy6FWMtN8fpL+KhWbyxH3OvizO6g8lPcFpu3ujz64dzZWCMBZT8dP8YRV3moJk+0ul81/5LbuwKmz1H1SRE+iH+nej0hapOxXQN2YpxZjy0gYshp2jcT+RHaJ8yMPksMXxVxBARBvEmq88LXvyPpHfbCURP7u454U4sPG0qzWwujQJLDS0lsnTb3HBXE02Ag5z3SXNvY/6OTp+C5J+Xq6ztI9HAMlRecaP6SvYDRcitoljnV1AeIAQPx0nuvYdYHGk+rK+qj1Xdvq8hZ+PV5F98Unz7ImS0v0B19a/mijp3b0gwVkPnX1ou1JQhibpOy+I05yKha/ke+tze/IgXWWHc7LcEhiscd9E64Jjj9ar81tbC4hLZdgblDOCS9FurZDnMJNvDCIQJpKcq2iho1MjlWNHxIBKtboSWwUCa8vU2srCwrx8TaLRAA2GSZS6tpgqxFA3mwRU1S1nCcgZZpJs7nF2gD1+zZbW23pUPufbdC1TH+vDnfmd+gzdcJonPRsI9UDsbFEGWz/1M2nR7Pwv+CcsheHj2oQbdAC/wrDr8bPJB7kCXtm17Kst/YnL4SfbWoATn8Jl6QF76YyRUH+xfNNE+wJkxqTd52PYPuJ+gX+ZJi51W93EoG3MAAnPUG6Gq6JFpqqWHZBYh4t3x3Ev+w6+O1Aj/+x8E0VLesphIbszwP9m6u4w55U/G1IMrn94PvKtdfsEs7PHQixrE/87SEV+Ep8tEFvHm+STXGjCpvpT0E55x1sSl22RhZAUMZTxMcZ2gQsuSvRVKWuvSyk1k1trD7pChKMQy+tIZrN1BlgtNbZDyT8t5X1ZbCLY5/GseDm6+m6Bw+CEYIQKq5BYJElt+BGzRt5lKWO7/oXslw3imnrflu+ju+LkcY2rG+EIv/+R3A6wb2v89czlpjSkKcJMdXGi+D8l9dvnht9Vhyolj8c5YqMgmVen5moOBiftmb/q3nhJVWsJPN6XSMxmh4f+D2IjcW2BeCacXSdN+Ysl7x1JJFujH1JUmKhPLHCVprJoQYHIAc2gWentc4fAMKw4AYcs9SKyZAlF+FkpOYZhcbGeXrVsLwTU9dtrl/OnRN8yILyiQ8pKKPPQduFtIbPOD7OEBm1IJ3x16ekfZr0MZqZyIO7/h3QBjz6vWwPQV3/IGBVKMHzSE5Y235OSHQAV4OugYBtei6jS5xfo1pk97SDMS9LrDncA4iGHjhAfBzzvISFQBmhnUPrSibNLW9O+5tX+fcJ3IxtFRcmAlNSjIDLWblS7YS4NgeS3k7DbfCOjHiFGYxvObXLk0IS0kFLwZWIvklEKiW61fIGeng66XsJqCsuMvyD6m66sC04l43ljHYGa5A/HGt6YCT6w51UzmqkG/lLnrqMXhWFTiucO6kmNfHKoBPwngjSvTx9gYDmVyohR3E3fq6IXruYU8FQvt5KvwSB+l2frmWyOyE+rWXpJ16XWksy3w8EjX8yQDVooDvdwYcS9WTX4deKM+I+zoklZNOjASJ+pUMCTAwpC0UJ6ocMaoDcsdYQyxsKSML52W8kLoaBNd2Ni8Tb6VtH2DV2X52SEroMzfK6jw/wFDkEx60v1P49SvxESV1N+IKg7cfP4ctt0DRH18L5oJyflizNjmSIlRZ50ovDDz1KQfu/+kbZDeJmtptVmzkdnRR59DVan9T9T4LDS1RQ5RC4MJ4LJT2vkzz6vngeB6PxKehDkVZvgQMH5elx5Dnd/R7BzeZXdjqS7uPPKg7iggv+vKmfdMFpQoKSoZ/CyP2/b6+scMJn+CYp/NRMFqllFBgp4qayyuqWrbfDi9X2+FWnPHsiYvH64fBx6VvXgQaXmTxXJtwh2mCwlV3WX2VXHlPmSV+gCcghGV+xMMXrQ2+tH9k253cd0gMakcsJgpS81K7Eo1QTJ4UgEWiEWqRNJucgpzRkUtt/V8DxkSQffHfrBbTsvGdCnVCXkfBZJIrEaGo8Da92HNZg7WyA2lhzSsQlNZbo3oqNWlpGX+ahN3iPMSStH9yiQ7scQUKYHtEscNTyntDeXDLKxoKruJhppKr8cDqTpyhnjsXj5BnYlRUGvME8zH2UiYVjYey9opriouW1U2NsXLJdRHRayYlj5FITrRXf+ubINDCYw4Uf9URizWXJ994drTMo+i9OXDVv0bRYIHqDFAmBt1Yrk59nBAdq3g++jL2amLDa9BPPpTY5uPk1J0qgpWhE4q9Iw7MeRVMwIBLpAOZzKRFce9FONbnmgdphDspMc80JFbjEW6liSkPhelGkLzuXYimV9WxSRWQSuwDNhvYpMHb44zFZqNmA8kjTCumb/aATpi2AQIJ4Zko5AVjJ/Qb7iHKFOSItJTw4Di32nIqc9MojYLQFWxzNaLJmyQwTAC3xXUSjATYqQ7iAFoYHCMkeVO68ZAI2YbcFqvstL2iQm5F8TPZaDYr1PHWjTTQPb8WKEtvrUOsJAgl3u9g5vhXLKdKVA5EvuagebAzg6tx3PUQpm7umzxiYC+XtstXP1PbgU/8yPfrLVUuvOFPrCdxGPDhLek6ccDGIg4EP93Jjzh0EmC+2xEUd+ZTkVziaZKHVQci+glNUxuoe5CSd5X6pn3/2Nj2nU3TAi9G9htbW7z8P9wiceoxeoFI2IUDPrXjHqP2sgukBq5ocwPHSOtdM5+arTLNBGW3ImZWYh3WKyeLm0rxzBxQA9R1QZ8PRdtSD9qEKO40exyD7bVzi4OaF1HOzvQD7ZhqpboPiyLELKZKixVEfb4AsrFx24pdUQo2eiaOiIoT+ftElHkS6GxUSu9MOA/d2BB5wedIO6oCA8EhCzOP3UeoahYCnG5oxa70Rx4iis/jLVhVHs3imoAoMYjK/EBtpSoXGt9Q4r2EIOZLJ8GuCWa+KPewKZ3rukmWXCNxnUDo9Z2HQ3YO5Q58AWvWPZSQ6KIgHbuXtJDfhqrEvjw8LcWFxXfuyrStmxS6bdGqkGiW5qXqPkusSXsQtKqaHnQJT68spkBV09Mcfky5oNjoKTHTBs41vSyb46xe5HUqfFkmh63uBUtWQJKJHdKbgH+m/jkFzEgAuZV4vuxuql382szb8CthUog4tRgAMraBcQ4o6QIAeUE2KXd+aNw6wwoIz8ZnhHTfgUM5fk3mZKKwrLzed7wcZxobOd0jcEX7AKsdJ0n2Io9KxbvEMhtfAz2kxa+djsZYHCMtmWoBIB19xlxEGm1id5nVZKib29Ql2mcSgBoB7r7zG7+MJxxdVNWIVYjAMlEnz5C9Oqm3OWKSde9Qm3HLDq9EICkDhkxEZsMCJSUbpg1oI1ZOetWGTB/yKDi6o/n3EQAXqf/oOYAY0lxKi3zDyKlDwi2TUgZYyFQYOtWe05PJYdzQCjLbz4kXxdg3i8WnyTsmfnIixYtKwShdC2jimKU47QRLzMfL/DLvymCjIUdHOoS9SDgknWraXnR3eAfm4Goq6ApcsEtI1f1UvtKpgRYyPWNA72FQmcTAAAAAAA"
)
PIPSPOOL_PAGE_ICON_SVG = (
    "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'>"
    "<g fill='none' stroke='#fff2d2' stroke-width='4.5' stroke-linecap='round' "
    "stroke-linejoin='round' transform='rotate(7 32 32)'>"
    "<rect x='8' y='13' width='48' height='38' rx='12'/>"
    "<rect x='13' y='18' width='38' height='28' rx='9'/>"
    "<path d='M8 27H4v10h4M56 27h4v10h-4'/>"
    "</g><g fill='none' stroke='#00dce7' stroke-width='4' "
    "stroke-linecap='round' transform='rotate(7 32 32)'>"
    "<circle cx='25' cy='30' r='3'/><circle cx='39' cy='30' r='3'/>"
    "<path d='M26 38q6 6 12 0'/></g></svg>"
)

PIP_HAPPY_DATA_URI = "data:image/webp;base64,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"
PIP_SAD_DATA_URI = "data:image/webp;base64,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"

PLUGIN_DIR = Path(__file__).resolve().parent
ORCA_DATA_DIR = next(
    (parent for parent in (PLUGIN_DIR, *PLUGIN_DIR.parents) if parent.name == "OrcaSlicer"),
    PLUGIN_DIR,
)
PERSISTENT_DIR = ORCA_DATA_DIR / "pipspool"
SETTINGS_PATH = PERSISTENT_DIR / SETTINGS_FILENAME
PAGE_ICON_PATH = PERSISTENT_DIR / "pipspool_page_icon.svg"
LOG_PATH = PERSISTENT_DIR / LOG_FILENAME


def legacy_settings_paths() -> list[Path]:
    """Find settings stored beside replaceable plugin files by older builds."""
    candidates = {PLUGIN_DIR / SETTINGS_FILENAME}
    plugin_root = ORCA_DATA_DIR / "orca_plugins"
    if plugin_root.is_dir():
        try:
            candidates.update(plugin_root.rglob(SETTINGS_FILENAME))
        except OSError:
            pass
    result = []
    for path in candidates:
        try:
            if path != SETTINGS_PATH and path.is_file():
                result.append(path)
        except OSError:
            continue
    return sorted(result, key=lambda path: path.stat().st_mtime)


def write_settings_payload(payload: dict[str, Any]) -> None:
    SETTINGS_PATH.parent.mkdir(parents=True, exist_ok=True)
    temporary = SETTINGS_PATH.with_suffix(".tmp")
    temporary.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    os.replace(temporary, SETTINGS_PATH)


def log(message: str) -> None:
    try:
        LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
        with LOG_PATH.open("a", encoding="utf-8") as stream:
            stream.write(f"{message}\n")
    except OSError:
        return


def normalize_url(value: str) -> str:
    value = str(value or "").strip().rstrip("/")
    if not value:
        raise ValueError("Spoolman URL cannot be empty")
    if not value.startswith(("http://", "https://")):
        raise ValueError("Spoolman URL must begin with http:// or https://")
    return value


def load_settings() -> dict[str, Any]:
    settings: dict[str, Any] = {
        "spoolman_url": DEFAULT_SPOOLMAN_URL,
        "show_pipspool_page": True,
        "inject_spool_id_gcode": True,
        "low_stock_threshold_grams": DEFAULT_LOW_STOCK_THRESHOLD_GRAMS,
    }
    migrated = False
    sources = [SETTINGS_PATH] if SETTINGS_PATH.is_file() else legacy_settings_paths()
    for source in sources:
        try:
            stored = json.loads(source.read_text(encoding="utf-8"))
            if isinstance(stored, dict):
                settings.update(stored)
                migrated = source != SETTINGS_PATH
        except (OSError, ValueError, TypeError):
            continue
    if migrated:
        try:
            write_settings_payload(settings)
            log(f"[SETTINGS] Migrated persistent settings to {SETTINGS_PATH}")
        except OSError as exc:
            log(f"[SETTINGS MIGRATION] {exc}")
    return settings


def pipspool_page_enabled() -> bool:
    return load_settings().get("show_pipspool_page", True) is not False


def low_stock_threshold(settings: dict[str, Any] | None = None) -> float:
    value = (settings or load_settings()).get(
        "low_stock_threshold_grams", DEFAULT_LOW_STOCK_THRESHOLD_GRAMS
    )
    threshold = numeric(value)
    if threshold is None or threshold < 0:
        return DEFAULT_LOW_STOCK_THRESHOLD_GRAMS
    return round(threshold, 1)


def spool_id_gcode_enabled(settings: dict[str, Any] | None = None) -> bool:
    return (settings or load_settings()).get("inject_spool_id_gcode", True) is not False


def spool_table_columns(settings: dict[str, Any] | None = None) -> list[str]:
    value = (settings or load_settings()).get("spool_table_columns")
    if not isinstance(value, list):
        return list(DEFAULT_SPOOL_TABLE_COLUMNS)
    return [column for column in SPOOL_TABLE_COLUMNS if column in value]


def restart_required(settings: dict[str, Any] | None = None) -> bool:
    """Keep the notice for this Orca process and clear it on the next launch."""
    current = settings or load_settings()
    return (
        current.get("restart_required") is True
        and current.get("restart_required_process_id") == os.getpid()
    )


def version_numbers(value: Any) -> tuple[int, int, int] | None:
    match = re.match(r"^v?(\d+)\.(\d+)\.(\d+)", str(value or "").strip())
    return tuple(int(part) for part in match.groups()) if match else None


def available_update(settings: dict[str, Any] | None = None) -> str | None:
    latest = str((settings or load_settings()).get("latest_available_version") or "")
    installed_numbers = version_numbers(PLUGIN_VERSION)
    latest_numbers = version_numbers(latest)
    if installed_numbers and latest_numbers and latest_numbers > installed_numbers:
        return latest.lstrip("v")
    return None


def check_for_update(force: bool = False) -> str | None:
    """Refresh the cached public release version without affecting core sync."""
    settings = load_settings()
    checked_at = numeric(settings.get("update_checked_at")) or 0
    if not force and time.time() - checked_at < UPDATE_CHECK_INTERVAL_SECONDS:
        return available_update(settings)
    update = {"update_checked_at": time.time()}
    try:
        response = HTTP_SESSION.get(
            LATEST_RELEASE_API,
            headers={"Accept": "application/vnd.github+json"},
            timeout=4,
        )
        response.raise_for_status()
        tag = str(response.json().get("tag_name") or "").strip()
        if version_numbers(tag):
            update["latest_available_version"] = tag.lstrip("v")
    except Exception as exc:
        log(f"[UPDATE CHECK] {exc}")
    try:
        save_settings(update)
    except Exception as exc:
        log(f"[UPDATE CACHE] {exc}")
    settings.update(update)
    return available_update(settings)


def has_saved_settings() -> bool:
    try:
        stored = json.loads(SETTINGS_PATH.read_text(encoding="utf-8"))
        return isinstance(stored, dict) and bool(
            normalize_url(stored.get("spoolman_url", ""))
        )
    except (OSError, ValueError, TypeError):
        return False


def save_settings(settings: dict[str, Any]) -> None:
    payload = load_settings()
    payload.update(settings)
    payload["spoolman_url"] = normalize_url(payload.get("spoolman_url", ""))
    payload.pop("moonraker_url", None)
    payload.pop("moonraker_enabled", None)
    write_settings_payload(payload)


def safe_filename(value: str) -> str:
    cleaned = re.sub(r'[\\/:*?"<>|]', "", str(value)).strip()
    return cleaned or "Unnamed spool"


def spool_id_from_name(filename: str) -> int | None:
    match = re.search(r"\(#(\d+)\)", filename)
    return int(match.group(1)) if match else None


def decode_extra_value(value: Any) -> Any:
    decoded = value
    for _ in range(2):
        if not isinstance(decoded, str):
            break
        try:
            next_value = json.loads(decoded)
        except (TypeError, ValueError):
            break
        if next_value == decoded:
            break
        decoded = next_value
    return decoded


def managed_start_gcode(
    existing: Any,
    spool_id: int,
    custom_gcode: Any = None,
    inject_spool_id: bool = True,
) -> list[str]:
    if isinstance(existing, list):
        text = str(existing[0]) if existing else ""
    else:
        text = "" if existing is None else str(existing)

    for begin, end in (
        (START_MARKER, END_MARKER),
        (LEGACY_START_MARKER, LEGACY_END_MARKER),
    ):
        pattern = re.compile(
            rf"(?:\r?\n)?{re.escape(begin)}.*?{re.escape(end)}(?:\r?\n)?",
            re.DOTALL,
        )
        text = pattern.sub("\n", text)

    preserved = text.rstrip()
    custom_text = decode_extra_value(custom_gcode)
    if custom_text is None:
        custom_text = ""
    custom_text = str(custom_text).strip()
    if not inject_spool_id and custom_text:
        custom_text = "\n".join(
            line for line in custom_text.splitlines()
            if not re.match(r"^\s*SET_SPOOL_ID(?:\s|$)", line, re.IGNORECASE)
        ).strip()
    managed_text = custom_text or (
        f"SET_SPOOL_ID ID={int(spool_id)}" if inject_spool_id else ""
    )
    if not managed_text:
        return [preserved]
    block = f"{START_MARKER}\n{managed_text}\n{END_MARKER}"
    return [f"{preserved}\n\n{block}" if preserved else block]


def support_directory() -> Path | None:
    for parent in (PLUGIN_DIR, *PLUGIN_DIR.parents):
        if parent.name == "OrcaSlicer":
            return parent

    appdata = os.environ.get("APPDATA")
    candidates = [
        Path.home() / "Library" / "Application Support" / "OrcaSlicer",
        Path.home() / ".config" / "OrcaSlicer",
    ]
    if appdata:
        candidates.append(Path(appdata) / "OrcaSlicer")
    return next((path for path in candidates if path.is_dir()), None)


@dataclass
class SyncReport:
    active_spools: int = 0
    created: int = 0
    updated: int = 0
    renamed: int = 0
    removed: int = 0
    unchanged: int = 0
    changes: list[str] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    restart_required: bool = False

    @property
    def changed(self) -> bool:
        return bool(self.created or self.updated or self.renamed or self.removed)

    @property
    def changed_spools(self) -> int:
        """Count logical spools, not copies written to Orca profile folders."""
        return len({
            int(match.group(1))
            for change in self.changes
            if (match := re.match(r"^Spool #(\d+):", change))
        })

    def summary(self) -> str:
        details = (
            f"Active spools: {self.active_spools}\n"
            f"Created: {self.created}\nUpdated: {self.updated}\n"
            f"Renamed: {self.renamed}\nRemoved: {self.removed}\n"
            f"Unchanged: {self.unchanged}"
        )
        if self.errors:
            details += f"\nErrors: {len(self.errors)}\n" + "\n".join(self.errors[:5])
        if self.changes:
            details += "\n\nChanges:\n" + "\n".join(
                f"• {change}" for change in self.changes
            )
        return details


class SpoolmanClient:
    def __init__(self, base_url: str):
        self.base_url = normalize_url(base_url)

    def active_spools(self) -> list[dict[str, Any]]:
        response = HTTP_SESSION.get(
            f"{self.base_url}/api/v1/spool",
            params={"allow_archived": "false"},
            timeout=10,
        )
        response.raise_for_status()
        payload = response.json()
        if not isinstance(payload, list):
            raise ValueError("Spoolman returned an unexpected spool response")
        return [
            item
            for item in payload
            if isinstance(item, dict) and not spool_is_archived(item)
        ]

    def ensure_start_gcode_field(self) -> bool:
        response = HTTP_SESSION.get(f"{self.base_url}/api/v1/field/spool", timeout=10)
        response.raise_for_status()
        fields = response.json()
        if not isinstance(fields, list):
            raise ValueError("Spoolman returned an unexpected extra-field response")

        existing = next(
            (field for field in fields if isinstance(field, dict) and field.get("key") == "start_gcode"),
            None,
        )
        if existing is not None:
            if existing.get("field_type") != "text":
                raise ValueError("Spoolman field 'start_gcode' exists but is not a text field")
            return False

        response = HTTP_SESSION.post(
            f"{self.base_url}/api/v1/field/spool/start_gcode",
            json={"name": "Start G-code", "field_type": "text", "order": 0},
            timeout=10,
        )
        response.raise_for_status()
        return True

    def ensure_orca_filament_fields(self, selected_settings=ORCA_SETTINGS) -> int:
        response = HTTP_SESSION.get(f"{self.base_url}/api/v1/field/filament", timeout=10)
        response.raise_for_status()
        fields = response.json()
        if not isinstance(fields, list):
            raise ValueError("Spoolman returned an unexpected filament-field response")
        existing = {
            field.get("key"): field for field in fields if isinstance(field, dict)
        }
        created = 0
        order = 100
        selected = set(selected_settings)
        for group, settings in ORCA_SETTING_GROUPS.items():
            for setting in settings:
                if setting not in selected:
                    continue
                key = f"{ORCA_FIELD_PREFIX}{setting}"
                label = setting.replace("_", " ").title()
                unit = ORCA_SETTING_UNITS.get(setting)
                field_type = orca_setting_field_type(setting)
                desired = {
                    "name": f"{group}: {label}",
                    "field_type": field_type,
                    "order": order,
                }
                if unit and field_type in {"integer", "float"}:
                    desired["unit"] = unit
                if field_type == "choice":
                    desired["choices"] = list(ORCA_CHOICE_SETTINGS[setting])
                    desired["multi_choice"] = False
                field = existing.get(key)
                if field is not None:
                    if field.get("field_type") != field_type:
                        self._replace_field_definition_safely(
                            setting, key, field, desired
                        )
                        order += 1
                        continue
                    if any(field.get(name) != value for name, value in desired.items()):
                        response = HTTP_SESSION.post(
                            f"{self.base_url}/api/v1/field/filament/{key}",
                            json=desired,
                            timeout=10,
                        )
                        response.raise_for_status()
                    order += 1
                    continue
                response = HTTP_SESSION.post(
                    f"{self.base_url}/api/v1/field/filament/{key}",
                    json=desired,
                    timeout=10,
                )
                response.raise_for_status()
                created += 1
                order += 1
        return created

    def _validated_field_value_migrations(
        self, setting: str, key: str
    ) -> list[tuple[int, str, str]]:
        """Preflight old Text values before changing a PipSpool field type."""
        response = HTTP_SESSION.get(f"{self.base_url}/api/v1/filament", timeout=10)
        response.raise_for_status()
        filaments = response.json()
        if not isinstance(filaments, list):
            raise ValueError("Spoolman returned an unexpected filament response")
        migrations: list[tuple[int, str, str]] = []
        for filament in filaments:
            if not isinstance(filament, dict):
                continue
            raw = dict(filament.get("extra") or {}).get(key)
            if raw is None:
                continue
            encoded = encode_spoolman_setting_value(setting, decode_extra_value(raw))
            if encoded is None:
                raise ValueError(
                    f"Spoolman field '{key}' contains a value that cannot be "
                    f"converted safely; its type was not changed"
                )
            migrations.append((int(filament["id"]), encoded, raw))
        return migrations

    def _replace_field_definition_safely(
        self,
        setting: str,
        key: str,
        existing: dict[str, Any],
        desired: dict[str, Any],
    ) -> None:
        """Replace an incompatible field and restore the original on failure."""
        migrations = self._validated_field_value_migrations(setting, key)
        original = {
            name: existing[name]
            for name in (
                "name", "field_type", "order", "unit", "default_value",
                "choices", "multi_choice",
            )
            if name in existing and existing[name] is not None
        }
        endpoint = f"{self.base_url}/api/v1/field/filament/{key}"
        deleted = False
        try:
            response = HTTP_SESSION.delete(endpoint, timeout=10)
            response.raise_for_status()
            deleted = True
            response = HTTP_SESSION.post(endpoint, json=desired, timeout=10)
            response.raise_for_status()
            for filament_id, encoded, _original_raw in migrations:
                self.update_filament_extras(filament_id, {key: encoded})
        except Exception as migration_error:
            if not deleted:
                raise
            try:
                # Remove a partially created replacement. A failed creation may
                # legitimately leave no definition, in which case 404 is safe.
                response = HTTP_SESSION.delete(endpoint, timeout=10)
                if getattr(response, "status_code", 200) != 404:
                    response.raise_for_status()
                response = HTTP_SESSION.post(endpoint, json=original, timeout=10)
                response.raise_for_status()
                for filament_id, _encoded, original_raw in migrations:
                    self.update_filament_extras(
                        filament_id, {key: original_raw}
                    )
            except Exception as rollback_error:
                raise RuntimeError(
                    f"Spoolman field '{key}' migration failed and its automatic "
                    f"rollback also failed: {rollback_error}"
                ) from migration_error
            raise RuntimeError(
                f"Spoolman field '{key}' migration failed; its original Text "
                "definition and values were restored"
            ) from migration_error

    def remove_unselected_orca_filament_fields(self, selected_settings) -> int:
        selected_keys = {orca_extra_key(setting) for setting in selected_settings}
        response = HTTP_SESSION.get(f"{self.base_url}/api/v1/field/filament", timeout=10)
        response.raise_for_status()
        fields = response.json()
        if not isinstance(fields, list):
            raise ValueError("Spoolman returned an unexpected filament-field response")
        removed = 0
        for field in fields:
            key = field.get("key") if isinstance(field, dict) else None
            if not isinstance(key, str) or not key.startswith(ORCA_FIELD_PREFIX):
                continue
            if key in selected_keys:
                continue
            response = HTTP_SESSION.delete(
                f"{self.base_url}/api/v1/field/filament/{key}", timeout=10
            )
            response.raise_for_status()
            removed += 1
        return removed

    def update_filament_extras(self, filament_id: int, values: dict[str, str]) -> None:
        response = HTTP_SESSION.patch(
            f"{self.base_url}/api/v1/filament/{int(filament_id)}",
            json={"extra": values},
            timeout=10,
        )
        response.raise_for_status()


class OrcaProfiles:
    def __init__(self, root: Path):
        self.root = root
        self.user_root = root / "user"
        self.system_root = root / "system"
        self.system_presets = self._system_preset_index()

    def _system_preset_index(self) -> dict[str, dict[str, Any]]:
        result: dict[str, dict[str, Any]] = {}
        if not self.system_root.is_dir():
            return result
        for path in self.system_root.rglob("*.json"):
            if "filament" not in path.parts:
                continue
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
                if not isinstance(data, dict):
                    continue
                # Filenames are only a compatibility fallback. They must never
                # replace an authoritative identity supplied inside another
                # Orca system preset (which can otherwise hide all children).
                result.setdefault(path.stem, data)
                if not path.stem.casefold().endswith("@system"):
                    result.setdefault(f"{path.stem} @System", data)
                aliases = set()
                name = data.get("name")
                if isinstance(name, str) and name.strip():
                    aliases.add(name.strip())
                settings_ids = data.get("filament_settings_id")
                if isinstance(settings_ids, str) and settings_ids.strip():
                    aliases.add(settings_ids.strip())
                elif isinstance(settings_ids, list):
                    aliases.update(
                        value.strip() for value in settings_ids
                        if isinstance(value, str) and value.strip()
                    )
                for alias in tuple(aliases):
                    result[alias] = data
                    if not alias.casefold().endswith("@system"):
                        result[f"{alias} @System"] = data
            except (OSError, ValueError, TypeError):
                continue
        return result

    def user_filament_directories(self) -> list[Path]:
        if not self.user_root.is_dir():
            return []
        directories = []
        for profile_root in self.user_root.iterdir():
            if profile_root.is_dir():
                directories.append(profile_root / "filament")
        return directories

    def parent_for(self, vendor: str, material: str) -> str:
        material_key = material.strip().casefold()
        material_text = material.strip()
        vendor_key = vendor.strip()

        # Prefer Orca's live preset bundle. Recent Orca builds store
        # system presets in .opc files rather than individual JSON files.
        try:
            collection = orca.host.preset_bundle().filaments
            names = {
                str(name).strip().casefold(): str(name)
                for name in collection.preset_names()
            }

            # Build the same material-type index used by the JSON fallback,
            # but from Orca's live system presets.
            live_presets_by_type: dict[str, list[str]] = {}
            live_type_names: dict[str, str] = {}
            for name in collection.preset_names():
                preset = collection.find_preset(name)
                if preset is None or not preset.is_system:
                    continue
                types_serialized = preset.config_value("filament_type")
                if not isinstance(types_serialized, str):
                    continue
                for value in types_serialized.split(";"):
                    type_name = value.strip()
                    type_key = type_name.casefold()
                    if type_key:
                        live_presets_by_type.setdefault(type_key, []).append(str(name))
                        live_type_names.setdefault(type_key, type_name)

            # First choice: vendor-specific exact system preset.
            if vendor_key:
                vendor_parent = f"{vendor_key} {material_text} @System"
                found = names.get(vendor_parent.casefold())
                if found:
                    return found

            # Second choice: generic exact system preset.
            generic_parent = f"Generic {material_text} @System"
            found = names.get(generic_parent.casefold())
            if found:
                return found

            # Preserve the existing compatible-material logic: choose the
            # longest material type that is a complete prefix of the material.
            compatible_types = [
                type_key for type_key in live_presets_by_type
                if material_key.startswith(type_key)
                and len(material_key) > len(type_key)
                and not material_key[len(type_key)].isalnum()
            ]
            if compatible_types:
                compatible_type = max(compatible_types, key=len)
                type_name = live_type_names[compatible_type]

                # Third choice: vendor-specific compatible material type.
                if vendor_key:
                    vendor_parent = f"{vendor_key} {type_name} @System"
                    found = names.get(vendor_parent.casefold())
                    if found:
                        return found

                # Fourth choice: generic compatible material type.
                generic_parent = f"Generic {type_name} @System"
                found = names.get(generic_parent.casefold())
                if found:
                    return found

        except Exception as exc:
            log(f"[ORCA PARENT PRESET] {exc}")

        # Fallback for older Orca builds where system presets are
        # available as JSON files.
        presets_by_type: dict[str, list[str]] = {}
        for name, preset in self.system_presets.items():
            types = preset.get("filament_type") or []
            if isinstance(types, str):
                types = [types]
            for value in types:
                type_key = str(value).strip().casefold()
                if type_key:
                    presets_by_type.setdefault(type_key, []).append(name)

        parent_type = material_key
        matching = presets_by_type.get(parent_type, [])
        if not matching:
            compatible_types = [
                type_key for type_key in presets_by_type
                if material_key.startswith(type_key)
                and len(material_key) > len(type_key)
                and not material_key[len(type_key)].isalnum()
            ]
            if compatible_types:
                parent_type = max(compatible_types, key=len)
                matching = presets_by_type[parent_type]

        if not matching:
            parent_type = "pla"
            matching = presets_by_type.get(parent_type, [])

        exact_generic = f"generic {parent_type} @system"
        for name in matching:
            if name.strip().casefold() == exact_generic:
                return name

        # Never accept a printer-specific preset merely because its name begins
        # with "Generic PETG" (or another material). Orca hides children of that
        # parent whenever a different printer is active.
        return f"Generic {parent_type.upper()} @System"
    def effective_preset(self, preset: dict[str, Any]) -> dict[str, Any]:
        chain = []
        current = preset
        visited: set[str] = set()
        while isinstance(current, dict):
            chain.append(current)
            parent_name = current.get("inherits")
            if not isinstance(parent_name, str) or not parent_name or parent_name in visited:
                break
            visited.add(parent_name)
            current = self.system_presets.get(parent_name)
            if current is None:
                break
        resolved: dict[str, Any] = {}
        for item in reversed(chain):
            resolved.update(item)
        return resolved

    def preset_for_spool(self, spool_id: int) -> dict[str, Any]:
        for directory in self.user_filament_directories():
            for path in directory.glob("*.json"):
                if spool_id_from_name(path.name) == int(spool_id):
                    return read_json(path)
        return {}

    def inherited_start_gcode(self, preset: dict[str, Any]) -> Any:
        visited: set[str] = set()
        parent_name = preset.get("inherits")
        while isinstance(parent_name, str) and parent_name and parent_name not in visited:
            visited.add(parent_name)
            parent = self.system_presets.get(parent_name)
            if not parent:
                break
            if "filament_start_gcode" in parent:
                return parent["filament_start_gcode"]
            parent_name = parent.get("inherits")
        return []


def filament_material(filament: dict[str, Any]) -> str:
    return str(filament.get("material") or "PLA").strip()


def orca_extra_key(setting: str) -> str:
    return f"{ORCA_FIELD_PREFIX}{setting}"


def decoded_orca_overrides(
    filament: dict[str, Any], selected_settings=ORCA_SETTINGS
) -> dict[str, Any]:
    extras = dict(filament.get("extra") or {})
    result = {}
    for setting in selected_settings:
        value = decode_extra_value(extras.get(orca_extra_key(setting)))
        if setting in ORCA_LIST_TEXT_SETTINGS:
            result[setting] = normalized_orca_text_list(value)
            continue
        if value not in (None, ""):
            values = value if isinstance(value, list) else [value]
            converted = [
                orca_serialized_setting_value(setting, item) for item in values
            ]
            converted = [item for item in converted if item is not None]
            if converted:
                result[setting] = (
                    converted[0]
                    if setting in ORCA_SCALAR_TEXT_SETTINGS
                    else converted
                )
    return result


def orca_serialized_setting_value(setting: str, value: Any) -> str | None:
    """Convert a typed Spoolman scalar to Orca's serialized vector element."""
    encoded = encode_spoolman_setting_value(setting, value)
    if encoded is None:
        return None
    native = json.loads(encoded)
    field_type = orca_setting_field_type(setting)
    if field_type == "boolean":
        return "1" if native else "0"
    if field_type == "integer":
        return str(int(native))
    if field_type == "float":
        return format(float(native), ".15g")
    return str(native)


def normalized_orca_text_list(value: Any) -> list[str]:
    """Normalize Orca list fields and discard nested/quoted empty entries."""
    decoded = value
    for _ in range(4):
        if not isinstance(decoded, str):
            break
        stripped = decoded.strip()
        if not stripped:
            return []
        try:
            next_value = json.loads(stripped)
        except (TypeError, ValueError):
            break
        if next_value == decoded:
            break
        decoded = next_value

    items = decoded if isinstance(decoded, (list, tuple)) else [decoded]
    normalized: list[str] = []
    for item in items:
        nested = item
        for _ in range(4):
            if not isinstance(nested, str):
                break
            stripped = nested.strip()
            if not stripped:
                nested = ""
                break
            try:
                next_value = json.loads(stripped)
            except (TypeError, ValueError):
                break
            if next_value == nested:
                break
            nested = next_value
        if isinstance(nested, (list, tuple)):
            normalized.extend(normalized_orca_text_list(nested))
            continue
        text = str(nested).strip() if nested is not None else ""
        if text:
            normalized.append(text)
    return normalized


def malformed_empty_orca_text_list(value: Any) -> bool:
    """Identify the quoted-empty list emitted by PipSpool 2.2.7."""
    decoded = decode_extra_value(value)
    return (
        isinstance(decoded, (list, tuple))
        and bool(decoded)
        and not normalized_orca_text_list(decoded)
    )


def encode_spoolman_setting_value(setting: str, value: Any) -> str | None:
    """Encode one Orca filament value for its semantic Spoolman field type."""
    if setting in ORCA_LIST_TEXT_SETTINGS:
        if value is None:
            return None
        values = normalized_orca_text_list(value)
        serialized_list = json.dumps(
            values,
            separators=(",", ":"),
        )
        # Spoolman decodes an extra value once before validating its field
        # type. Keep Orca's JSON list inside a JSON string so a Text field sees
        # text rather than a raw list; decode_extra_value restores the list.
        return json.dumps(serialized_list, separators=(",", ":"))
    if isinstance(value, (list, tuple)):
        if not value:
            return None
        value = value[0]
    if value is None or value == "":
        return None

    field_type = orca_setting_field_type(setting)
    try:
        if field_type == "boolean":
            if isinstance(value, str):
                normalized = value.strip().casefold()
                if normalized in {"1", "true", "yes", "on"}:
                    value = True
                elif normalized in {"0", "false", "no", "off"}:
                    value = False
                else:
                    return None
            else:
                value = bool(value)
        elif field_type == "integer":
            value = int(float(value))
        elif field_type == "float":
            value = float(value)
        elif field_type == "choice":
            choices = ORCA_CHOICE_SETTINGS[setting]
            if isinstance(value, (int, float)) or str(value).strip().isdigit():
                index = int(value)
                if not 0 <= index < len(choices):
                    return None
                value = choices[index]
            else:
                value = str(value)
                if value not in choices:
                    return None
        else:
            value = str(value)
    except (TypeError, ValueError, OverflowError):
        return None
    return json.dumps(value, separators=(",", ":"))


def numeric(value: Any) -> float | None:
    if value is None or value == "":
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def spool_is_archived(spool: dict[str, Any]) -> bool:
    value = spool.get("archived", False)
    if isinstance(value, str):
        return value.strip().casefold() in {"1", "true", "yes", "on"}
    return bool(value)


def desired_preset(
    spool: dict[str, Any],
    existing: dict[str, Any],
    profiles: OrcaProfiles,
    selected_settings=ORCA_SETTINGS,
    inject_spool_id: bool = True,
) -> tuple[str, dict[str, Any]]:
    spool_id = int(spool["id"])
    filament = spool.get("filament") or {}
    vendor_data = filament.get("vendor") or {}
    vendor = str(vendor_data.get("name") or "Generic").strip()
    filament_name = str(filament.get("name") or filament_material(filament)).strip()
    material = filament_material(filament)
    material_prefix = re.compile(rf"^{re.escape(material)}(?:\s+|$)", re.IGNORECASE)
    filament_detail = material_prefix.sub("", filament_name, count=1).strip()
    material_and_name = f"{material} {filament_detail}".strip()
    display_name = f"(#{spool_id}) {material_and_name} - {vendor} - PipSpool"

    preset = dict(existing)
    dependency_values = {
        key: preset[key]
        for key in ORCA_DEPENDENCY_KEYS
        if key in preset and key not in selected_settings
    }
    desired_parent = profiles.parent_for(vendor, material)
    # Reapply PipSpool's portable base on every sync. This also repairs profiles
    # whose parent was set to a printer-specific preset by an older build.
    preset["inherits"] = desired_parent

    start_gcode = preset.get("filament_start_gcode")
    if start_gcode is None:
        start_gcode = profiles.inherited_start_gcode(preset)

    color = str(filament.get("color_hex") or "FFFFFF").lstrip("#")
    spool_extras = dict(spool.get("extra") or {})
    preset.update(
        {
            "name": display_name,
            "from": "User",
            "version": "2.5.0.0",
            "filament_settings_id": [display_name],
            "filament_vendor": [vendor],
            "filament_type": [material],
            "default_filament_colour": [f"#{color}"],
            "filament_start_gcode": managed_start_gcode(
                start_gcode,
                spool_id,
                spool_extras.get("start_gcode"),
                inject_spool_id,
            ),
        }
    )

    nozzle = numeric(filament.get("settings_extruder_temp"))
    if nozzle and nozzle > 0:
        temperature = str(round(nozzle))
        preset["nozzle_temperature"] = [temperature]
        preset["nozzle_temperature_initial_layer"] = [temperature]

    bed = numeric(filament.get("settings_bed_temp"))
    if bed and bed > 0:
        temperature = str(round(bed))
        for plate_key in (
            "supertack_plate_temp",
            "cool_plate_temp",
            "textured_cool_plate_temp",
            "eng_plate_temp",
            "hot_plate_temp",
            "textured_plate_temp",
        ):
            preset[plate_key] = [temperature]
            preset[f"{plate_key}_initial_layer"] = [temperature]

    price = numeric(spool.get("price"))
    if price is None:
        price = numeric(filament.get("price"))
    weight = numeric(filament.get("weight"))
    if price is not None and weight and weight > 0:
        preset["filament_cost"] = [f"{price * 1000 / weight:.2f}"]

    extras = dict(filament.get("extra") or {})
    extras.update(spool_extras)
    max_flow = numeric(decode_extra_value(extras.get("max_volumetric_speed")))
    if max_flow is not None and max_flow > 0:
        preset["filament_max_volumetric_speed"] = [str(max_flow)]

    # Only apply advanced values after synchronize_filament_settings has
    # reconciled both sides. Raw Spoolman data must never win by accident.
    if filament.get("_pipspool_advanced_values_reconciled") is True:
        # Selected dependencies are jointly managed. Remove an old local value
        # first so an empty Spoolman value clears a bad Orca restriction.
        for key in ORCA_DEPENDENCY_KEYS:
            if key in selected_settings:
                preset.pop(key, None)
        preset.update(decoded_orca_overrides(filament, selected_settings))

    # Preserve restrictions unless the user explicitly selected that dependency
    # field for synchronization. Unselected compatibility remains Orca-owned.
    preset.update(dependency_values)

    return display_name, preset


def host_filament_preset_snapshot(
    selected_settings=ORCA_SETTINGS,
) -> dict[str, dict[str, Any]]:
    """Copy Orca's resolved preset values while the host handle is safe to read."""
    snapshot: dict[str, dict[str, Any]] = {}
    try:
        collection = orca.host.preset_bundle().filaments
        for name in collection.preset_names():
            preset = collection.find_preset(name)
            if preset is None:
                continue
            keys = set(preset.config_keys())
            values = {}
            for setting in selected_settings:
                if setting not in keys:
                    continue
                value = preset.config_value(setting)
                if value is not None:
                    values[setting] = value
            if values:
                snapshot[str(name)] = values
    except Exception as exc:
        log(f"[ORCA PRESET SNAPSHOT] {exc}")
    return snapshot


def synchronize_filament_settings(
    spools: list[dict[str, Any]],
    profiles: OrcaProfiles,
    client: SpoolmanClient,
    reset: bool = False,
    selected_settings=ORCA_SETTINGS,
    live_preset_values: dict[str, dict[str, Any]] | None = None,
    sync_state: dict[str, dict[str, str]] | None = None,
    change_directions: dict[str, set[int]] | None = None,
) -> int:
    """Reconcile advanced fields using the last successful value as baseline."""
    sync_state = sync_state if isinstance(sync_state, dict) else {}
    if change_directions is not None:
        change_directions.setdefault("orca_to_spoolman", set())
        change_directions.setdefault("spoolman_to_orca", set())
    grouped: dict[int, list[dict[str, Any]]] = {}
    for spool in spools:
        filament = spool.get("filament") or {}
        if filament.get("id") is not None:
            grouped.setdefault(int(filament["id"]), []).append(spool)

    updated = 0
    for filament_id, filament_spools in grouped.items():
        example = filament_spools[0]
        filament = example.get("filament") or {}
        vendor = str((filament.get("vendor") or {}).get("name") or "Generic").strip()
        material = filament_material(filament)
        local_master = profiles.preset_for_spool(int(example["id"]))
        master = local_master
        if not master:
            parent = profiles.parent_for(vendor, material)
            master = profiles.system_presets.get(parent, {"inherits": parent})
            local_master = {}
        master = profiles.effective_preset(master)
        live_preset_values = live_preset_values or {}
        # The host snapshot contains Orca's resolved values, while JSON files
        # commonly contain only local overrides. Apply parent first and the
        # spool's own preset last so Orca remains authoritative.
        live_names = (
            profiles.parent_for(vendor, material),
            str(master.get("inherits") or ""),
            str(master.get("name") or ""),
        )
        for preset_name in live_names:
            if preset_name in live_preset_values:
                master.update({
                    key: value
                    for key, value in live_preset_values[preset_name].items()
                    if key not in ORCA_DEPENDENCY_KEYS
                })
        extras = dict(filament.get("extra") or {})
        patch_values: dict[str, str] = {}
        filament_state = sync_state.setdefault(str(filament_id), {})
        for stale_setting in set(filament_state) - set(selected_settings):
            filament_state.pop(stale_setting, None)
        for setting in selected_settings:
            key = orca_extra_key(setting)
            current = decode_extra_value(extras.get(key))
            current_encoded = encode_spoolman_setting_value(setting, current)
            # A value inherited from a system parent is not a local Orca
            # choice. Do not promote that restriction onto every filament.
            if setting in ORCA_DEPENDENCY_KEYS and setting not in local_master:
                if current_encoded is not None:
                    filament_state[setting] = current_encoded
                continue
            if setting not in master:
                continue
            encoded = encode_spoolman_setting_value(setting, master[setting])
            if encoded is None:
                continue
            baseline = filament_state.get(setting)
            if reset or baseline is None:
                agreed = encoded
            elif current_encoded == encoded:
                agreed = encoded
            elif encoded == baseline and current_encoded is not None:
                # Orca stayed at the last synchronized value, so Spoolman was
                # edited and becomes the new agreed value for this field.
                agreed = current_encoded
                if change_directions is not None:
                    change_directions["spoolman_to_orca"].update(
                        int(spool["id"]) for spool in filament_spools
                    )
            else:
                # Orca changed, or both sides changed differently. Orca wins a
                # genuine conflict because it is the declared master.
                agreed = encoded
            if current_encoded != agreed or (
                setting in ORCA_LIST_TEXT_SETTINGS
                and malformed_empty_orca_text_list(extras.get(key))
            ):
                patch_values[key] = agreed
                if change_directions is not None:
                    change_directions["orca_to_spoolman"].update(
                        int(spool["id"]) for spool in filament_spools
                    )
            extras[key] = agreed
            filament_state[setting] = agreed
        if not filament_state:
            sync_state.pop(str(filament_id), None)
        if patch_values:
            client.update_filament_extras(filament_id, patch_values)
            updated += 1
        for spool in filament_spools:
            spool_filament = spool.get("filament") or {}
            spool_filament["extra"] = dict(extras)
            spool_filament["_pipspool_advanced_values_reconciled"] = True
    return updated


def read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else {}
    except (OSError, ValueError, TypeError):
        return {}


def write_json_atomic(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def add_report_change(report: SyncReport, message: str) -> None:
    """Add a user-facing change once, even when Orca has several user folders."""
    if message not in report.changes:
        report.changes.append(message)


def changed_profile_fields(existing: dict[str, Any], desired: dict[str, Any]) -> str:
    """Describe meaningful preset changes in short, human-readable terms."""
    changed = {
        key
        for key in set(existing) | set(desired)
        if existing.get(key) != desired.get(key)
    }
    labels: list[str] = []
    groups = (
        ("profile base", {"inherits"}),
        ("name", {"name", "filament_settings_id"}),
        ("material", {"filament_type"}),
        ("manufacturer", {"filament_vendor"}),
        ("colour", {"default_filament_colour"}),
        ("start G-code", {"filament_start_gcode"}),
        (
            "nozzle temperature",
            {"nozzle_temperature", "nozzle_temperature_initial_layer"},
        ),
        (
            "bed temperature",
            {
                key
                for key in changed
                if key.endswith("_plate_temp")
                or key.endswith("_plate_temp_initial_layer")
            },
        ),
        ("cost", {"filament_cost"}),
        ("maximum volumetric speed", {"filament_max_volumetric_speed"}),
    )
    described: set[str] = {"version", "from"}
    for label, keys in groups:
        matching = changed & keys
        if matching:
            labels.append(label)
            described.update(matching)
    labels.extend(key.replace("_", " ") for key in sorted(changed - described))
    return ", ".join(labels) if labels else "profile data"


def sync_profiles(
    spools: list[dict[str, Any]],
    profiles: OrcaProfiles,
    selected_settings=ORCA_SETTINGS,
    change_directions: dict[str, set[int]] | None = None,
    inject_spool_id: bool = True,
) -> SyncReport:
    spools = [spool for spool in spools if not spool_is_archived(spool)]
    report = SyncReport(active_spools=len(spools))
    orca_to_spoolman = (
        change_directions.get("orca_to_spoolman", set())
        if change_directions else set()
    )
    spoolman_to_orca = (
        change_directions.get("spoolman_to_orca", set())
        if change_directions else set()
    )
    active_ids = {int(spool["id"]) for spool in spools if spool.get("id") is not None}
    empty_inventory_warning_added = False

    for directory in profiles.user_filament_directories():
        directory.mkdir(parents=True, exist_ok=True)
        files_by_id: dict[int, list[Path]] = {}
        for path in directory.glob("*.json"):
            spool_id = spool_id_from_name(path.name)
            if spool_id is not None and path.name.endswith((PROFILE_SUFFIX, " - Spoolman.json")):
                files_by_id.setdefault(spool_id, []).append(path)

        for spool in spools:
            try:
                spool_id = int(spool["id"])
                candidates = sorted(files_by_id.get(spool_id, []))
                source = candidates[0] if candidates else None
                existing = read_json(source) if source else {}
                display_name, data = desired_preset(
                    spool, existing, profiles, selected_settings, inject_spool_id
                )
                target = directory / f"{safe_filename(display_name)}.json"

                if source is None:
                    write_json_atomic(target, data)
                    report.created += 1
                    report.restart_required = True
                    add_report_change(
                        report, f"Spool #{spool_id}: created {display_name}."
                    )
                elif source != target:
                    write_json_atomic(target, data)
                    for old_path in candidates:
                        if old_path != target and old_path.exists():
                            old_path.unlink()
                    report.renamed += 1
                    report.restart_required = True
                    add_report_change(
                        report, f"Spool #{spool_id}: renamed to {display_name}."
                    )
                elif existing != data:
                    changed_keys = {
                        key for key in set(existing) | set(data)
                        if existing.get(key) != data.get(key)
                    }
                    changed_fields = changed_profile_fields(existing, data)
                    write_json_atomic(target, data)
                    for duplicate in candidates[1:]:
                        if duplicate.exists():
                            duplicate.unlink()
                    report.updated += 1
                    # An Orca edit exported to Spoolman may also normalize the
                    # preset JSON on disk. Orca already has that live value, so
                    # it must not produce a restart notice. Imports from
                    # Spoolman and all ordinary profile changes still do.
                    exported_from_live_orca = (
                        spool_id in orca_to_spoolman
                        and spool_id not in spoolman_to_orca
                    )
                    if not exported_from_live_orca:
                        report.restart_required = True
                    add_report_change(
                        report, f"Spool #{spool_id}: updated {changed_fields}."
                    )
                else:
                    report.unchanged += 1
            except Exception as exc:
                report.errors.append(f"Spool {spool.get('id', '?')}: {exc}")

        for spool_id, paths in files_by_id.items():
            if spool_id in active_ids:
                continue
            if not active_ids:
                if not empty_inventory_warning_added:
                    report.errors.append(
                        "Profile cleanup skipped because Spoolman returned zero active "
                        "spools. Existing PipSpool profiles were preserved."
                    )
                    empty_inventory_warning_added = True
                continue
            for path in paths:
                try:
                    path.unlink()
                    report.removed += 1
                    report.restart_required = True
                    add_report_change(
                        report, f"Spool #{spool_id}: removed archived profile."
                    )
                except OSError as exc:
                    report.errors.append(f"Remove {path.name}: {exc}")

    return report


LEGACY_PLUGIN_REFS = {
    "spoolman_bridge;;Filament Usage Updater",
    "Spoolman Bridge;3ad590dc-6698-4327-9005-12b977229ed2;Filament Usage Updater",
}


def remove_legacy_pipeline_artifacts(profiles: OrcaProfiles) -> tuple[int, int]:
    removed_processes = 0
    cleaned_presets = 0
    if not profiles.user_root.is_dir():
        return removed_processes, cleaned_presets

    for path in profiles.user_root.rglob("*.json"):
        if path.parent.name == "process" and path.name.endswith(" - SpoolMan.json"):
            path.unlink()
            removed_processes += 1
            continue

        data = read_json(path)
        changed = False
        refs = data.get("plugins")
        if isinstance(refs, list):
            filtered = [ref for ref in refs if ref not in LEGACY_PLUGIN_REFS]
            if filtered != refs:
                changed = True
                if filtered:
                    data["plugins"] = filtered
                else:
                    data.pop("plugins", None)
        elif refs in LEGACY_PLUGIN_REFS:
            data.pop("plugins", None)
            changed = True

        pipeline = data.get("slicing_pipeline_plugin")
        if isinstance(pipeline, list):
            filtered = [name for name in pipeline if name != "Filament Usage Updater"]
            if filtered != pipeline:
                changed = True
                if filtered:
                    data["slicing_pipeline_plugin"] = filtered
                else:
                    data.pop("slicing_pipeline_plugin", None)
        elif pipeline == "Filament Usage Updater":
            data.pop("slicing_pipeline_plugin", None)
            changed = True

        if changed:
            write_json_atomic(path, data)
            cleaned_presets += 1

    return removed_processes, cleaned_presets


def orca_profiles() -> OrcaProfiles:
    root = support_directory()
    if root is None:
        raise RuntimeError("OrcaSlicer profile directory could not be found")
    return OrcaProfiles(root)


def show_message(message: str, title: str = "PipSpool", icon: str = "info") -> None:
    orca.host.ui.message(message, title=title, icon=icon)


def parse_field_config(value: Any) -> tuple[tuple[str, ...], bool]:
    try:
        config = json.loads(value) if isinstance(value, str) else value
    except (TypeError, ValueError):
        config = {}
    if not isinstance(config, dict):
        config = {}
    requested = config.get("selected_fields", [])
    if not isinstance(requested, list):
        requested = []
    selected = tuple(setting for setting in ORCA_SETTINGS if setting in requested)
    return selected, bool(config.get("remove_unselected_fields", False))


def field_config_html() -> str:
    groups = []
    for group, settings in ORCA_SETTING_GROUPS.items():
        options = "".join(
            f'<label><input type="checkbox" value="{escape(setting)}">'
            f'<span>{escape(setting.replace("_", " ").title())}</span></label>'
            for setting in settings
        )
        groups.append(
            f'<section><div class="group"><h2>{escape(group)}</h2>'
            f'<button onclick="setGroup(this,true)">All</button>'
            f'<button onclick="setGroup(this,false)">None</button></div>'
            f'<div class="fields">{options}</div></section>'
        )
    return f"""<!doctype html><html><head>
<meta name="viewport" content="width=device-width,initial-scale=1">
<style>
body{{margin:0;padding:18px;background:#25262a;color:#f4f4f4;font:14px system-ui,sans-serif}}
.intro{{color:#c9cbd0;line-height:1.45;margin:0 0 14px}}section{{border-top:1px solid #444;padding:12px 0}}
.group{{display:flex;align-items:center;gap:7px}}h2{{font-size:15px;margin:0 auto 0 0}}
button{{border:1px solid #62656b;border-radius:5px;background:#36383d;color:#eee;padding:4px 10px}}
.fields{{display:grid;grid-template-columns:repeat(auto-fit,minmax(245px,1fr));gap:7px 16px;margin-top:10px}}
label{{display:flex;align-items:center;gap:8px;min-height:24px}}input{{accent-color:#00a99d}}
.danger{{margin-top:14px;padding:11px;border:1px solid #80534c;border-radius:6px;background:#3b2b29}}
.actions{{position:sticky;bottom:0;display:flex;justify-content:flex-end;padding-top:15px;background:#25262a}}
.save{{background:#008c82;border-color:#00b7aa;padding:7px 18px}}
</style></head><body>
<p class="intro">Choose the Orca filament settings PipSpool may copy to Spoolman. No advanced fields are selected by default. Spool identity, material, colour, temperature, price and spool-ID G-code continue to work normally.</p>
{''.join(groups)}
<label class="danger"><input id="remove" type="checkbox"><span><b>Remove unselected PipSpool fields from Spoolman</b><br>This deletes their saved values for every filament the next time Sync Spoolman Profiles runs.</span></label>
<div class="actions"><button class="save" onclick="save()">Save selection</button></div>
<script>
function setGroup(button,state){{button.closest('section').querySelectorAll('input').forEach(x=>x.checked=state)}}
async function load(){{
 let value=await window.orca.getConfig();
 try{{if(typeof value==='string')value=JSON.parse(value)}}catch(e){{value={{}}}}
 value=value||{{}}; const selected=new Set(value.selected_fields||[]);
 document.querySelectorAll('.fields input').forEach(x=>x.checked=selected.has(x.value));
 document.getElementById('remove').checked=!!value.remove_unselected_fields;
}}
async function save(){{
 const selected=[...document.querySelectorAll('.fields input:checked')].map(x=>x.value);
 await window.orca.saveConfig(JSON.stringify({{selected_fields:selected,remove_unselected_fields:document.getElementById('remove').checked}}));
}}
load();
</script></body></html>"""


def sync_with_spoolman(
    selected_settings: tuple[str, ...], remove_unselected: bool = False,
    live_preset_values: dict[str, dict[str, Any]] | None = None,
) -> tuple[SyncReport, list[dict[str, Any]]]:
    if live_preset_values is None:
        live_preset_values = host_filament_preset_snapshot(selected_settings)
    settings = load_settings()
    sync_state = settings.get("advanced_sync_state")
    if not isinstance(sync_state, dict):
        sync_state = {}
    save_settings({"selected_fields": list(selected_settings)})
    client = SpoolmanClient(settings["spoolman_url"])
    field_warning = None
    try:
        client.ensure_start_gcode_field()
        client.ensure_orca_filament_fields(selected_settings)
        if remove_unselected:
            client.remove_unselected_orca_filament_fields(selected_settings)
    except Exception as exc:
        field_warning = f"Spoolman field setup: {exc}"
        log(f"[FIELD SETUP WARNING] {exc}")
    spools = client.active_spools()
    profiles = orca_profiles()
    change_directions: dict[str, set[int]] = {}
    try:
        synchronize_filament_settings(
            spools, profiles, client, selected_settings=selected_settings,
            live_preset_values=live_preset_values,
            sync_state=sync_state,
            change_directions=change_directions,
        )
    except Exception as exc:
        warning = f"Filament setting sync: {exc}"
        field_warning = f"{field_warning}; {warning}" if field_warning else warning
        log(f"[FILAMENT SETTING WARNING] {exc}")
    report = sync_profiles(
        spools, profiles, selected_settings,
        change_directions=change_directions,
        inject_spool_id=spool_id_gcode_enabled(settings),
    )
    if field_warning:
        report.errors.insert(0, field_warning)
    report_data = {
        "active_spools": report.active_spools,
        "created": report.created,
        "updated": report.updated,
        "renamed": report.renamed,
        "removed": report.removed,
        "unchanged": report.unchanged,
        "changes": list(report.changes),
        "changed_spools": report.changed_spools,
        "errors": list(report.errors),
        "changed": report.changed,
        "restart_required": report.restart_required,
    }
    saved_state = {
        "last_sync_report": report_data,
        "advanced_sync_state": sync_state,
    }
    if report.restart_required:
        saved_state.update({
            "restart_required": True,
            "restart_required_process_id": os.getpid(),
        })
    save_settings(saved_state)
    log(f"[SYNC] {report.summary().replace(chr(10), '; ')}")
    return report, spools


def save_advanced_field_selection(
    selected_settings: tuple[str, ...],
    live_preset_values: dict[str, dict[str, Any]] | None = None,
) -> tuple[int, int]:
    """Save enabled fields and establish their two-way synchronization state."""
    save_settings({"selected_fields": list(selected_settings)})
    settings = load_settings()
    sync_state = settings.get("advanced_sync_state")
    if not isinstance(sync_state, dict):
        sync_state = {}
    client = SpoolmanClient(settings["spoolman_url"])
    created = client.ensure_orca_filament_fields(selected_settings)
    spools = client.active_spools()
    populated = synchronize_filament_settings(
        spools,
        orca_profiles(),
        client,
        selected_settings=selected_settings,
        live_preset_values=live_preset_values,
        sync_state=sync_state,
    )
    save_settings({"advanced_sync_state": sync_state})
    return created, populated


class SyncCapability(orca.script.ScriptPluginCapabilityBase):
    def get_name(self):
        return "Sync Spoolman Profiles"

    def has_config_ui(self):
        return True

    def get_config_ui(self):
        return field_config_html()

    def get_default_config(self):
        return {"selected_fields": [], "remove_unselected_fields": False}

    def get_config_version(self):
        return FIELD_CONFIG_VERSION

    def execute(self):
        try:
            selected_settings, remove_unselected = parse_field_config(self.get_config())
        except Exception as exc:
            log(f"[FIELD CONFIG WARNING] {exc}")
            selected_settings, remove_unselected = (), False
        cached_fields = load_settings().get("selected_fields", [])
        if not selected_settings and isinstance(cached_fields, list):
            selected_settings = tuple(
                setting for setting in ORCA_SETTINGS if setting in cached_fields
            )
        live_preset_values = host_filament_preset_snapshot(selected_settings)

        def work():
            try:
                report, _spools = sync_with_spoolman(
                    selected_settings, remove_unselected, live_preset_values
                )
                suffix = "\n\nRestart OrcaSlicer to load changed presets." if report.changed else ""
                show_message(report.summary() + suffix, icon="warning" if report.errors else "info")
            except Exception as exc:
                log(f"[SYNC ERROR] {exc}")
                show_message(f"Synchronization failed:\n{exc}", icon="error")

        threading.Thread(target=work, daemon=True).start()
        return orca.ExecutionResult.success("PipSpool synchronization started")


class ResetFilamentSettingsCapability(orca.script.ScriptPluginCapabilityBase):
    def get_name(self):
        return "Reset Spoolman Filament Settings from Orca"

    def execute(self):
        settings = load_settings()
        selected_settings = tuple(
            setting for setting in ORCA_SETTINGS
            if setting in settings.get("selected_fields", [])
        )
        live_preset_values = host_filament_preset_snapshot(selected_settings)
        sync_state = settings.get("advanced_sync_state")
        if not isinstance(sync_state, dict):
            sync_state = {}

        def work():
            try:
                client = SpoolmanClient(settings["spoolman_url"])
                client.ensure_orca_filament_fields(selected_settings)
                spools = client.active_spools()
                profiles = orca_profiles()
                updated = synchronize_filament_settings(
                    spools, profiles, client, reset=True,
                    selected_settings=selected_settings,
                    live_preset_values=live_preset_values,
                    sync_state=sync_state,
                )
                save_settings({"advanced_sync_state": sync_state})
                report = sync_profiles(spools, profiles, selected_settings)
                show_message(
                    f"Reset {updated} Spoolman filament record(s) from Orca.\n\n"
                    + report.summary()
                )
            except Exception as exc:
                log(f"[FILAMENT RESET ERROR] {exc}")
                show_message(f"Filament setting reset failed:\n{exc}", icon="error")

        threading.Thread(target=work, daemon=True).start()
        return orca.ExecutionResult.success("PipSpool filament setting reset started")


class LegacyCleanupCapability(orca.script.ScriptPluginCapabilityBase):
    def get_name(self):
        return "Remove Legacy Double Profiles"

    def execute(self):
        try:
            removed, cleaned = remove_legacy_pipeline_artifacts(orca_profiles())
            message = (
                f"Removed {removed} legacy process profile(s).\n"
                f"Cleaned {cleaned} legacy preset reference(s).\n\n"
                "Synced PipSpool filament presets were preserved. Restart OrcaSlicer."
            )
            show_message(message)
            return orca.ExecutionResult.success(message)
        except Exception as exc:
            return orca.ExecutionResult.failure(
                orca.PluginResult.RecoverableError,
                f"Legacy cleanup failed: {exc}",
            )


def profile_sync_statuses(
    spools: list[dict[str, Any]],
    profiles: OrcaProfiles,
    selected_settings=ORCA_SETTINGS,
    sync_state: dict[str, dict[str, str]] | None = None,
    inject_spool_id: bool = True,
) -> dict[int, dict[str, str]]:
    """Compare active Spoolman spools with Orca's actually loaded user presets."""

    # Ask Orca which filament presets are actually loaded.
    # This avoids guessing whether user\default or user\<UUID> is active.
    active_files_by_id: dict[int, list[Path]] = {}

    try:
        bundle = orca.host.preset_bundle()
        filaments = bundle.filaments

        for index in range(filaments.size()):
            preset = filaments.preset(index)

            if not preset.is_user():
                continue

            if not preset.file:
                continue

            source = Path(preset.file)

            # Only consider PipSpool-style filament profiles.
            if not source.name.endswith(
                (PROFILE_SUFFIX, " - Spoolman.json")
            ):
                continue

            spool_id = spool_id_from_name(source.name)
            if spool_id is None:
                continue

            active_files_by_id.setdefault(spool_id, []).append(source)

    except Exception as exc:
        log(f"[PROFILE STATUS] Could not inspect Orca loaded presets: {exc!r}")
        return {
            int(spool["id"]): {
                "status": "error",
                "warning": (
                    "PipSpool could not inspect Orca's loaded filament presets. "
                    "Check the PipSpool log for details."
                ),
            }
            for spool in spools
            if spool.get("id") is not None
        }

    result: dict[int, dict[str, str]] = {}
    sync_state = sync_state if isinstance(sync_state, dict) else {}

    for spool in spools:
        if spool.get("id") is None:
            continue

        spool_id = int(spool["id"])
        candidates = sorted(active_files_by_id.get(spool_id, []))

        if not candidates:
            result[spool_id] = {
                "status": "profile_missing",
                "warning": (
                    f"The active Orca profile for spool #{spool_id} is missing. "
                    "Select Synchronize now, then restart OrcaSlicer."
                ),
            }
            continue

        missing = False
        update_required = False
        comparison_error = False

        # Orca normally has exactly one active user preset for a given spool.
        # Keep the duplicate detection from the old implementation.
        if len(candidates) > 1:
            update_required = True

        for source in candidates:
            directory = source.parent

            try:
                raw = json.loads(source.read_text(encoding="utf-8"))

                if not isinstance(raw, dict):
                    raise ValueError("profile root is not an object")

                display_name, desired = desired_preset(
                    spool,
                    raw,
                    profiles,
                    selected_settings,
                    inject_spool_id,
                )

                target = directory / f"{safe_filename(display_name)}.json"
                raw_for_compare = dict(raw)
                desired_for_compare = dict(desired)

                if "filament_cost" in raw_for_compare and "filament_cost" in desired_for_compare:
                    try:
                        raw_for_compare["filament_cost"] = [
                            f"{float(value):.2f}"
                            for value in raw_for_compare["filament_cost"]
                        ]
                        desired_for_compare["filament_cost"] = [
                            f"{float(value):.2f}"
                            for value in desired_for_compare["filament_cost"]
                        ]
                    except (TypeError, ValueError):
                        pass

                if source != target or raw_for_compare != desired_for_compare:
                    update_required = True
                filament = spool.get("filament") or {}
                baseline = sync_state.get(str(filament.get("id")), {})
                extras = filament.get("extra") or {}
                effective = profiles.effective_preset(raw)

                for setting in selected_settings:
                    agreed = baseline.get(setting)

                    if agreed is None or setting not in effective:
                        continue

                    orca_value = encode_spoolman_setting_value(
                        setting,
                        effective.get(setting),
                    )

                    spoolman_value = encode_spoolman_setting_value(
                        setting,
                        decode_extra_value(
                            extras.get(orca_extra_key(setting))
                        ),
                    )

                    if (
                        orca_value == agreed
                        and spoolman_value is not None
                        and spoolman_value != agreed
                    ):
                        update_required = True

                        break

            except (OSError, ValueError, TypeError):
                comparison_error = True

        if comparison_error:
            result[spool_id] = {
                "status": "error",
                "warning": (
                    f"PipSpool could not read or compare the active Orca profile "
                    f"for spool #{spool_id}. Synchronize again and check the "
                    "PipSpool log if the problem remains."
                ),
            }
        elif missing:
            result[spool_id] = {
                "status": "profile_missing",
                "warning": (
                    f"The active Orca profile for spool #{spool_id} is missing. "
                    "Select Synchronize now, then restart OrcaSlicer."
                ),
            def page_spool_data(
    spool: dict[str, Any], sync_status: dict[str, str] | None = None
) -> dict[str, Any]:
    filament = spool.get("filament") or {}
    vendor = filament.get("vendor") or {}
    remaining = numeric(spool.get("remaining_weight"))
    if remaining is None:
        remaining = numeric(spool.get("initial_weight"))
    initial_weight = numeric(spool.get("initial_weight"))
    if initial_weight is None or initial_weight <= 0:
        initial_weight = numeric(filament.get("weight"))
    remaining_percent = None
    remaining_step = None
    if remaining is not None and initial_weight is not None and initial_weight > 0:
        remaining_percent = max(0.0, min(100.0, remaining / initial_weight * 100.0))
        remaining_step = min(100, int(math.ceil(remaining_percent / 10.0) * 10))
    nozzle_temperature = numeric(filament.get("settings_extruder_temp"))
    bed_temperature = numeric(filament.get("settings_bed_temp"))
    data = {
        "id": spool.get("id"),
        "material": filament_material(filament),
        "name": str(filament.get("name") or "Unnamed filament"),
        "vendor": str(vendor.get("name") or "Generic"),
        "color": f"#{str(filament.get('color_hex') or 'FFFFFF').lstrip('#')}",
        "remaining": None if remaining is None else round(remaining, 1),
        "initial_weight": None if initial_weight is None else round(initial_weight, 1),
        "remaining_percent": None if remaining_percent is None else round(remaining_percent, 1),
        "remaining_step": remaining_step,
        "location": str(spool.get("location") or ""),
        "nozzle_temperature": (
            None if nozzle_temperature is None else round(nozzle_temperature, 1)
        ),
        "bed_temperature": (
            None if bed_temperature is None else round(bed_temperature, 1)
        ),
    }
    assignment = spool_gate_assignment(spool)
    if assignment is None:
        data.update({"loaded": False, "printer": "", "gate": None})
    else:
        printer, gate = assignment
        data.update({"loaded": True, "printer": printer, "gate": gate})
    if sync_status:
        data["sync_status"] = sync_status.get("status", "")
        data["sync_warning"] = sync_status.get("warning", "")
    else:
        data["sync_status"] = ""
        data["sync_warning"] = ""
    return data


def spool_gate_assignment(spool: dict[str, Any]) -> tuple[str, int] | None:
    """Return Spoolman's printer/gate assignment without contacting Moonraker."""
    extras = dict(spool.get("extra") or {})
    printer = str(decode_extra_value(extras.get("printer_name")) or "").strip()
    gate_value = numeric(decode_extra_value(extras.get("mmu_gate_map")))
    if gate_value is None:
        location = str(spool.get("location") or "")
        match = re.match(r"^\s*(.*?)\s*@\s*MMU Gate:\s*(-?\d+)\s*$", location)
        if match:
            printer = printer or match.group(1).strip()
            gate_value = numeric(match.group(2))
    if gate_value is None or gate_value < 0:
        return None
    return printer or "Printer", int(gate_value)


def page_gate_data(
    spool: dict[str, Any], sync_status: dict[str, str] | None = None
) -> dict[str, Any] | None:
    assignment = spool_gate_assignment(spool)
    if assignment is None:
        return None
    printer, gate = assignment
    data = page_spool_data(spool, sync_status)
    data.update({"printer": printer, "gate": gate})
    sync_warning = str(data.get("sync_warning") or "").strip()
    if sync_warning:
        data["warning"] = sync_warning
    return data


def gate_image_data_uri(color: str, gate: int, empty: bool = False) -> str:
    color = str(color or "#FFFFFF")
    if not re.fullmatch(r"#[0-9A-Fa-f]{6}", color):
        color = "#FFFFFF"
    filament_color = "#555b63" if empty else color
    svg = f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 72 58">
<path d="M19 10h34l11 10v24l-8 8H16l-8-8V20z" fill="#292d33" stroke="#737983" stroke-width="3" stroke-linejoin="round"/>
<rect x="29" y="3" width="14" height="10" rx="4" fill="#181a1e" stroke="#858b94" stroke-width="2"/>
<path d="M36 5v44" fill="none" stroke="{filament_color}" stroke-width="5" stroke-linecap="round"/>
<path d="M26 25l5-7h10l5 7-3 10-7 4-7-4z" fill="#17191c" stroke="#969ca5" stroke-width="2"/>
<circle cx="36" cy="28" r="11" fill="#17191c" stroke="#969ca5" stroke-width="2"/>
<text x="36" y="33" text-anchor="middle" fill="#f2f3f5" font-family="Segoe UI,Arial,sans-serif" font-size="14" font-weight="700">{int(gate)}</text>
<path d="M30 52h12l-3 5h-6z" fill="#17191c" stroke="#858b94" stroke-width="2" stroke-linejoin="round"/></svg>"""
    encoded = base64.b64encode(svg.encode("utf-8")).decode("ascii")
    return f"data:image/svg+xml;base64,{encoded}"


def page_gate_slots(gates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[str, dict[int, list[dict[str, Any]]]] = {}
    for gate in gates:
        grouped.setdefault(gate["printer"], {}).setdefault(gate["gate"], []).append(gate)
    slots = []
    for printer in sorted(grouped, key=str.casefold):
        assigned = grouped[printer]
        highest_gate = max(assigned)
        slot_count = max(8, ((highest_gate // 8) + 1) * 8)
        for gate_number in range(slot_count):
            if gate_number in assigned:
                candidates = sorted(
                    assigned[gate_number], key=lambda item: int(item.get("id") or 0)
                )
                selected = dict(candidates[0])
                if len(candidates) > 1:
                    spool_ids = ", ".join(f"#{candidate.get('id')}" for candidate in candidates)
                    duplicate_warning = (
                        f"Gate {gate_number} on {printer} is assigned to multiple "
                        f"active spools: {spool_ids}. Check the gate assignments in Spoolman."
                    )
                    existing_warning = str(selected.get("warning") or "").strip()
                    selected["warning"] = " ".join(
                        item for item in (existing_warning, duplicate_warning) if item
                    )
                slots.append(selected)
            else:
                slots.append({
                    "printer": printer,
                    "gate": gate_number,
                    "empty": True,
                    "color": "#555B63",
                })
    return slots


def pipspool_page_state(notice=None, friendly_initial_error=False) -> dict[str, Any]:
    settings = load_settings()
    try:
        spools = SpoolmanClient(settings["spoolman_url"]).active_spools()
        connected, detail = True, f"Found {len(spools)} active spool(s)."
    except Exception as exc:
        spools, connected = [], False
        detail = SPOOLMAN_CONNECTION_MESSAGE
        log(f"[PAGE CONNECTION ERROR] {exc}")
    log(
        f"[PAGE STATE] connected={connected}; url={settings.get('spoolman_url', DEFAULT_SPOOLMAN_URL)}; "
        f"detail={detail}"
    )
    selected_fields = tuple(
        setting for setting in ORCA_SETTINGS
        if setting in settings.get("selected_fields", [])
    )
    try:
        sync_state = settings.get("advanced_sync_state")
        statuses = profile_sync_statuses(
            spools, orca_profiles(), selected_fields,
            sync_state=sync_state if isinstance(sync_state, dict) else {},
            inject_spool_id=spool_id_gcode_enabled(settings),
        )
    except Exception as exc:
        log(f"[PROFILE STATUS ERROR] {exc}")
        statuses = {
            int(spool["id"]): {
                "status": "error",
                "warning": "PipSpool could not check this spool's Orca profile.",
            }
            for spool in spools if spool.get("id") is not None
        }
    gates = [
        gate for spool in spools
        if (gate := page_gate_data(spool, statuses.get(int(spool.get("id") or -1))))
    ]
    gates.sort(key=lambda item: (item["printer"].casefold(), item["gate"]))
    return {
        "type": "state",
        "connected": connected,
        "detail": notice or detail,
        "url": settings.get("spoolman_url", DEFAULT_SPOOLMAN_URL),
        "selected_fields": settings.get("selected_fields", []),
        "inject_spool_id_gcode": spool_id_gcode_enabled(settings),
        "low_stock_threshold": low_stock_threshold(settings),
        "spool_table_columns": spool_table_columns(settings),
        "restart_required": restart_required(settings),
        "synchronization_required": any(
            value.get("status") in {"profile_missing", "update_required"}
            for value in statuses.values()
        ),
        "available_update": available_update(settings),
        "last_report": settings.get("last_sync_report"),
        "spools": [
            page_spool_data(spool, statuses.get(int(spool.get("id") or -1)))
            for spool in spools
        ],
        "gates": page_gate_slots(gates),
    }


def pipspool_page_html(initial_state=None) -> str:
    if initial_state is None:
        initial_state = {
            "type": "state",
            "connected": False,
            "detail": "Connection state unavailable.",
            "selected_fields": [],
            "inject_spool_id_gcode": True,
            "low_stock_threshold": DEFAULT_LOW_STOCK_THRESHOLD_GRAMS,
            "spool_table_columns": list(DEFAULT_SPOOL_TABLE_COLUMNS),
            "last_report": None,
            "spools": [],
        }
    initial_state_json = json.dumps(initial_state).replace("</", "<\\/")
    initial_connected = initial_state.get("connected") is True
    initial_status = "Connection OK" if initial_connected else "Not connected"
    initial_detail = escape(str(initial_state.get("detail") or ""))
    initial_pip = PIP_HAPPY_DATA_URI if initial_connected else PIP_SAD_DATA_URI
    initial_spool_id_gcode = initial_state.get("inject_spool_id_gcode", True) is not False
    initial_spools = initial_state.get("spools") or []
    initial_gates = initial_state.get("gates") or []
    initial_low_stock_threshold = numeric(initial_state.get("low_stock_threshold"))
    if initial_low_stock_threshold is None or initial_low_stock_threshold < 0:
        initial_low_stock_threshold = DEFAULT_LOW_STOCK_THRESHOLD_GRAMS
    initial_table_columns = [
        column for column in SPOOL_TABLE_COLUMNS
        if column in initial_state.get(
            "spool_table_columns", DEFAULT_SPOOL_TABLE_COLUMNS
        )
    ]
    selected_fields = set(initial_state.get("selected_fields") or [])
    initial_report = initial_state.get("last_report")
    initial_restart_required = initial_state.get("restart_required") is True
    initial_synchronization_required = (
        initial_state.get("synchronization_required") is True
    )
    initial_available_update = initial_state.get("available_update")
    if isinstance(initial_report, dict):
        initial_active = initial_report.get("active_spools", len(initial_spools))
        initial_change_lines = [
            str(change) for change in initial_report.get("changes", [])
        ]
        initial_changed_ids = {
            int(match.group(1))
            for change in initial_change_lines
            if (match := re.match(r"^Spool #(\d+):", change))
        }
        initial_changed = int(
            initial_report.get("changed_spools", len(initial_changed_ids)) or 0
        )
        initial_errors = initial_report.get("errors") or []
        report_lines = [
            (
                f"{initial_changed} spool profile"
                f"{'s' if initial_changed != 1 else ''} changed."
                if initial_changed else "No spool profiles needed changes."
            )
        ]
        if initial_change_lines:
            report_lines.extend(("", *[f"• {change}" for change in initial_change_lines]))
        if initial_errors:
            report_lines.extend(("", "Errors:", *[f"• {error}" for error in initial_errors]))
        initial_report_text = "\n".join(report_lines)
    else:
        initial_active = len(initial_spools)
        initial_changed = "—"
        initial_errors = []
        initial_report_text = "No synchronization report yet."
    spool_rows = []
    for spool in initial_spools:
        color = str(spool.get("color") or "#FFFFFF")
        if not re.fullmatch(r"#[0-9A-Fa-f]{6}", color):
            color = "#FFFFFF"
        remaining = spool.get("remaining")
        remaining_text = "—" if remaining is None else f"{remaining} g"
        nozzle_temperature = spool.get("nozzle_temperature")
        nozzle_text = (
            "—" if nozzle_temperature is None else f"{nozzle_temperature} °C"
        )
        bed_temperature = spool.get("bed_temperature")
        bed_text = "—" if bed_temperature is None else f"{bed_temperature} °C"
        loaded_text = (
            f"{spool.get('printer') or 'Printer'} · Gate {spool.get('gate')}"
            if spool.get("loaded") and spool.get("gate") is not None else "—"
        )
        sync_status = str(spool.get("sync_status") or "")
        sync_text = {
            "synced": "Synced",
            "profile_missing": "Profile missing",
            "update_required": "Update required",
            "error": "Error",
        }.get(sync_status, "Unknown")
        sync_warning = escape(str(spool.get("sync_warning") or ""), quote=True)
        remaining_percent = numeric(spool.get("remaining_percent"))
        remaining_step = numeric(spool.get("remaining_step"))
        step = 0 if remaining_step is None else max(0, min(100, remaining_step))
        hue = max(0.0, min(120.0, (step - 10.0) / 90.0 * 120.0))
        remaining_title = (
            "Remaining percentage unavailable" if remaining_percent is None
            else f"{remaining_percent:g}% remaining; gauge shown in 10% steps"
        )
        fill_color = (
            "#31516d" if remaining_step is None else f"hsl({hue:g},46%,30%)"
        )
        remaining_html = (
            f'<span class="table-gauge" title="{escape(remaining_title, quote=True)}">'
            f'<span class="table-gauge-fill" style="width:{step:g}%;background:{fill_color}"></span>'
            f'<span class="table-gauge-copy">{escape(remaining_text)}</span></span>'
        )
        spool_rows.append(
            "<tr>"
            f'<td><button class="spool-link" data-open-spool="{escape(str(spool.get("id", "")), quote=True)}" title="Open this spool in Spoolman">#{escape(str(spool.get("id", "")))} ↗</button></td>'
            f"<td>{escape(str(spool.get('material') or ''))}</td>"
            f'<td data-column="filament">{escape(str(spool.get("name") or ""))}</td>'
            f'<td data-column="manufacturer">{escape(str(spool.get("vendor") or ""))}</td>'
            f'<td data-column="colour"><span class="swatch" style="background:{color}"></span>{escape(color)}</td>'
            f'<td data-column="nozzle">{escape(nozzle_text)}</td>'
            f'<td data-column="bed">{escape(bed_text)}</td>'
            f'<td data-column="remaining">{remaining_html}</td>'
            f'<td data-column="location">{escape(str(spool.get("location") or "—"))}</td>'
            f'<td data-column="loaded">{escape(loaded_text)}</td>'
            f'<td data-column="sync"><span class="profile-status profile-{escape(sync_status or "unknown", quote=True)}" title="{sync_warning}">{escape(sync_text)}</span></td></tr>'
        )
    spool_rows_html = "".join(spool_rows)
    loadout_cards = []
    for gate in initial_gates:
        color = str(gate.get("color") or "#FFFFFF")
        if not re.fullmatch(r"#[0-9A-Fa-f]{6}", color):
            color = "#FFFFFF"
        is_empty = gate.get("empty") is True
        gate_warning = str(gate.get("warning") or "").strip()
        has_problem = bool(gate_warning) and not is_empty
        remaining = gate.get("remaining")
        is_low = (
            not is_empty
            and initial_low_stock_threshold > 0
            and numeric(remaining) is not None
            and numeric(remaining) <= initial_low_stock_threshold
        )
        status = "Empty" if is_empty else f"Spool #{gate.get('id')}"
        material = "—" if is_empty else str(gate.get("material") or "Unknown")
        remaining_text = "" if is_empty else ("— g" if remaining is None else f"{remaining} g")
        remaining_percent = numeric(gate.get("remaining_percent"))
        remaining_step = numeric(gate.get("remaining_step"))
        gauge_html = ""
        if not is_empty:
            if remaining_step is None:
                fill_style = "width:0%;background:#31516d"
                gauge_title = "Remaining percentage unavailable"
            else:
                hue = max(0.0, min(120.0, (remaining_step - 10.0) / 90.0 * 120.0))
                fill_style = f"width:{remaining_step:g}%;background:hsl({hue:g},46%,30%)"
                gauge_title = f"{remaining_percent:g}% remaining; gauge shown in 10% steps"
            label_html = '<span class="gate-low-label">Low filament</span>' if is_low else ""
            gauge_html = (
                f'<span class="gate-gauge" title="{escape(gauge_title, quote=True)}">'
                f'<span class="gate-gauge-fill" style="{fill_style}"></span>'
                f'<span class="gate-gauge-copy">{label_html}'
                f'<span class="gate-grams">{escape(remaining_text)}</span></span></span>'
            )
        title_attribute = ""
        if has_problem:
            title_attribute = f' title="{escape(gate_warning, quote=True)}"'
        elif is_low:
            low_title = (
                f"Low filament: {remaining_text} remaining "
                f"(warning at {initial_low_stock_threshold:g} g)"
            )
            title_attribute = f' title="{escape(low_title, quote=True)}"'
        loadout_cards.append(
            f'<article class="gate-tile{" empty-gate" if is_empty else ""}{" gate-problem" if has_problem else ""}"'
            f'{title_attribute}>'
            f'<span class="gate-status">{escape(status)}</span>'
            f'<img class="gate-image" src="{gate_image_data_uri(color, int(gate.get("gate", 0)), is_empty)}" alt="Gate {escape(str(gate.get("gate", "")))}">'
            f'<b class="gate-material">{escape(material)}</b>'
            f'<span class="gate-printer">{escape(str(gate.get("printer") or "Printer"))}</span>'
            f'{gauge_html}</article>'
        )
    loadout_cards_html = "".join(loadout_cards)
    field_tabs = []
    field_panels = []
    for group_index, (group, fields) in enumerate(ORCA_SETTING_GROUPS.items()):
        group_count = sum(field in selected_fields for field in fields)
        choices = "".join(
            f'<label class="choice"><input type="checkbox" value="{escape(field)}"'
            f'{" checked" if field in selected_fields else ""}>'
            f'<span>{escape(field.replace("_", " ").title())}</span></label>'
            for field in fields
        )
        active_class = " active" if group_index == 0 else ""
        field_tabs.append(
            f'<button class="field-tab{active_class}" type="button" role="tab" '
            f'aria-selected="{"true" if group_index == 0 else "false"}" '
            f'data-field-tab="{escape(group)}">{escape(group)} '
            f'<span class="tab-count" data-tab-count="{escape(group)}">{group_count}</span></button>'
        )
        field_panels.append(
            f'<section class="field-panel{active_class}" role="tabpanel" '
            f'data-field-panel="{escape(group)}"{"" if group_index == 0 else " hidden"}>'
            f'<div class="field-panel-heading"><div><h3>{escape(group)}</h3>'
            f'<p class="muted">Choose the {escape(group.lower())} settings PipSpool may synchronize with Spoolman.</p></div>'
            f'<div class="group-actions"><button type="button" data-group-action="all">Select all</button>'
            f'<button type="button" data-group-action="none">Clear</button></div></div>'
            f'<div class="choices">{choices}</div></section>'
        )
    return f"""<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><style>
.pipspool-page{{--orca-bg:#030914;--orca-fg:#f5ead8;--orca-muted:#a9bfd4;--orca-accent:#168cff;--orca-accent-fg:#03101e;--orca-border:#1767a8;--panel:#08264b;--panel2:#061a33;--cyan:#42e5ea;--ivory:#f1dfc7;--amber:#f2a43a;--good:#67d39a;--warn:#f2a43a;--bad:#f07168}}
*{{box-sizing:border-box}}html{{height:100%;margin:0;background:#030914}}body.pipspool-page{{min-height:100%;margin:0;overflow:auto;background:radial-gradient(circle at 50% -220px,#0c407c 0,#061a34 360px,var(--orca-bg) 760px);color:var(--orca-fg);font:14px/1.45 var(--orca-font,system-ui,"Segoe UI",sans-serif)}}main{{max-width:1440px;margin:auto;padding:22px}}header{{display:flex;align-items:center;gap:15px;margin-bottom:18px;padding-bottom:13px;border-bottom:2px solid var(--amber)}}
.logo{{width:58px;height:58px;object-fit:contain}}h1{{font-size:23px;margin:0;color:var(--ivory)}}.sub{{color:var(--orca-muted);margin:2px 0 0}}
.top-actions{{margin-left:auto;display:flex;gap:9px}}body.pipspool-page button{{border:1px solid #277fc5;border-radius:7px;background:#0a315f;color:var(--ivory);padding:8px 13px;cursor:pointer;font-weight:600}}
body.pipspool-page button:hover{{background:#0d4788;border-color:#42a9ff}}body.pipspool-page button:disabled{{opacity:.5;cursor:default}}body.pipspool-page .primary{{background:var(--orca-accent);border-color:#5bb5ff;color:var(--orca-accent-fg);box-shadow:0 0 14px rgba(22,140,255,.28)}}
.grid{{display:grid;grid-template-columns:minmax(0,3fr) minmax(0,1fr);gap:16px}}.card{{background:linear-gradient(145deg,#0a315f,#061c38);border:1px solid #147fd1;border-top-color:#36a7ff;border-radius:12px;padding:17px;box-shadow:0 10px 28px rgba(0,42,91,.32),inset 0 1px rgba(120,198,255,.08)}}
.card h2{{font-size:16px;margin:0 0 12px;color:var(--ivory)}}.status-line{{display:flex;align-items:center;gap:16px;min-height:118px}}.status-pip{{width:116px;height:116px;object-fit:contain;filter:drop-shadow(0 5px 8px rgba(0,0,0,.3))}}.status-copy b{{display:block;font-size:18px;margin-bottom:4px;color:var(--cyan)}}body.pipspool-page input[type=search]{{width:100%;background:#041326;color:var(--orca-fg);border:1px solid #1a6eae;border-radius:7px;padding:9px 11px;outline:none}}
.connection-layout{{display:grid;grid-template-columns:minmax(270px,330px) minmax(0,1fr);gap:20px;align-items:start}}.connection-side{{min-width:0}}.gate-panel{{position:relative;min-width:0;padding-left:20px;border-left:1px solid var(--orca-border)}}.gate-panel h2{{margin-bottom:2px;color:var(--ivory)}}.gate-panel>p{{padding-right:235px}}
.spool-id-control{{position:absolute;top:-4px;right:0;display:flex;align-items:center;gap:10px;padding:7px 10px;border:1px solid #2385cf;border-radius:9px;background:#061a35;color:var(--ivory);cursor:pointer;box-shadow:0 4px 12px rgba(0,0,0,.2)}}.spool-id-control-copy{{display:flex;flex-direction:column;line-height:1.15}}.spool-id-control-copy b{{font-size:12px}}.spool-id-control-copy span{{margin-top:3px;color:var(--orca-muted);font-size:10px}}.switch{{position:relative;width:40px;height:22px;flex:0 0 auto}}.switch input{{position:absolute;opacity:0;pointer-events:none}}.switch-track{{position:absolute;inset:0;border:1px solid #57738d;border-radius:12px;background:#24384b;transition:.18s}}.switch-track:after{{content:"";position:absolute;top:3px;left:3px;width:14px;height:14px;border-radius:50%;background:#d8e3eb;transition:.18s}}.switch input:checked+.switch-track{{border-color:#36a7ff;background:#1177c5;box-shadow:0 0 10px rgba(54,167,255,.28)}}.switch input:checked+.switch-track:after{{transform:translateX(18px);background:white}}.spool-id-control:focus-within{{outline:2px solid var(--cyan);outline-offset:2px}}
body.pipspool-page input:focus{{border-color:var(--cyan);box-shadow:0 0 0 2px rgba(66,229,234,.16)}}.metrics{{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-top:12px}}.metric{{background:#061a35;border:1px solid #1766a5;border-radius:8px;padding:10px}}.metric b{{display:block;font-size:19px;color:var(--cyan)}}.metric span,.muted{{color:var(--orca-muted);font-size:12px}}
.report{{white-space:pre-wrap;background:#041326;border:1px solid #0d4f85;border-radius:8px;padding:11px;min-height:76px;color:#d7e7f4}}.toolbar{{display:flex;align-items:flex-start;gap:9px;margin-bottom:10px}}.toolbar input[type=search]{{flex:1}}.columns-menu{{position:relative;border:0;padding:0;flex:0 0 auto}}.columns-menu summary{{list-style:none;border:1px solid #277fc5;border-radius:7px;background:#0a315f;color:var(--ivory);padding:8px 13px;font-weight:600}}.columns-menu summary::-webkit-details-marker{{display:none}}.columns-menu[open] summary{{background:#0d4788}}.column-choices{{position:absolute;z-index:5;right:0;top:42px;width:210px;padding:10px;border:1px solid #2385cf;border-radius:9px;background:#061a35;box-shadow:0 10px 26px rgba(0,0,0,.45)}}.column-choices label{{display:flex;align-items:center;gap:8px;padding:5px 3px}}
.spool-link{{padding:2px 5px!important;border:0!important;background:transparent!important;color:#8fd0ff!important;font:inherit!important;white-space:nowrap}}.spool-link:hover{{color:var(--cyan)!important;text-decoration:underline}}.table-gauge{{position:relative;display:inline-flex;min-width:88px;min-height:25px;align-items:center;justify-content:center;overflow:hidden;border:1px solid #2789c7;border-radius:9px;background:#06213d}}.table-gauge-fill{{position:absolute;inset:0 auto 0 0}}.table-gauge-copy{{position:relative;z-index:1;font-size:12px;font-weight:650;color:#f4f5f6}}.profile-status{{display:inline-block;padding:3px 7px;border-radius:8px;background:#092746;color:#b9d5ea;white-space:nowrap}}.profile-synced{{color:#9dd8bd}}.profile-profile_missing,.profile-update_required,.profile-error{{border:1px solid #d65e58;background:#3a1c20;color:#ffd1cc}}
table{{width:100%;border-collapse:separate;border-spacing:0}}th,td{{padding:9px 8px;border-bottom:1px solid #175486;text-align:left}}th{{color:var(--orca-muted);font-size:12px}}.spool-wrap thead th{{position:sticky;top:0;z-index:2;background:#08264b;box-shadow:0 1px 0 #2385cf}}.swatch{{display:inline-block;width:14px;height:14px;border:1px solid #77a5c8;border-radius:50%;vertical-align:-2px;margin-right:7px}}
.gate-grid{{display:grid;grid-template-columns:repeat(8,minmax(108px,1fr));gap:10px;margin-top:14px}}.gate-tile{{min-width:0;min-height:184px;padding:11px 8px;border:1px solid #2385cf;border-radius:10px;background:linear-gradient(160deg,#0b3970,#061e3f);display:flex;flex-direction:column;align-items:center;text-align:center;box-shadow:0 5px 15px rgba(0,45,95,.28),inset 0 1px rgba(126,204,255,.1)}}.gate-status{{height:21px;color:#8fc8ff;font-size:11px}}.gate-image{{width:72px;height:58px;margin:3px 0 7px;display:block;filter:drop-shadow(0 4px 5px rgba(0,0,0,.32))}}.gate-material{{font-size:14px;line-height:1.2;color:var(--ivory)}}.gate-printer{{max-width:100%;margin-top:3px;color:var(--orca-muted);font-size:11px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}}.gate-alert{{margin-top:5px;color:#ffd37f;font-size:11px;font-weight:750}}.gate-remaining{{margin-top:auto;padding:3px 8px;border:1px solid #32a8eb;border-radius:10px;background:#08345a;color:var(--cyan);font-size:12px;font-weight:650}}.low-stock{{border-color:var(--amber);background:linear-gradient(160deg,#624014,#261b0c);box-shadow:0 0 0 1px rgba(242,164,58,.22),0 7px 18px rgba(90,52,0,.42),inset 0 1px rgba(255,221,158,.13)}}.low-stock .gate-remaining{{border-color:var(--amber);background:#4b300d;color:#ffe0a1}}.empty-gate{{opacity:.58}}.empty-gate .gate-status{{color:#d3d6da;font-size:13px;font-weight:700}}.empty-gate .gate-remaining{{visibility:hidden}}
.gate-gauge{{position:relative;width:100%;min-height:28px;margin-top:auto;overflow:hidden;border:1px solid #32a8eb;border-radius:10px;background:#041c31;color:#f8fbff;font-size:11px;font-weight:700;box-shadow:inset 0 1px 3px rgba(0,0,0,.4)}}.gate-gauge-fill{{position:absolute;inset:0 auto 0 0;transition:width .2s ease}}.gate-gauge-copy{{position:relative;z-index:1;min-height:26px;padding:2px 5px;display:flex;align-items:center;justify-content:center;gap:4px;line-height:1.05;text-shadow:0 1px 2px #000}}.gate-low-label{{display:block;font-size:9px;color:#fff0dd}}.gate-grams{{white-space:nowrap}}
.gate-problem{{border-color:var(--bad);box-shadow:0 0 0 1px rgba(240,113,104,.3),0 7px 18px rgba(92,17,17,.38),inset 0 1px rgba(255,190,185,.12)}}
.spool-wrap{{max-height:420px;overflow:auto}}.wide{{grid-column:1/-1}}details{{border-top:1px solid var(--orca-border);padding:11px 0}}summary{{cursor:pointer;font-weight:650}}
.field-tabs{{display:flex;align-items:flex-end;gap:24px;margin:17px 0 0;padding:0 4px;border-bottom:1px solid #1d6fae;overflow-x:auto}}body.pipspool-page .field-tab{{position:relative;flex:0 0 auto;border:0;border-radius:0;background:transparent;color:#8fa9c1;padding:10px 3px 11px;font-size:14px;font-weight:600;box-shadow:none}}body.pipspool-page .field-tab:hover{{border:0;background:transparent;color:var(--ivory)}}body.pipspool-page .field-tab.active{{color:var(--ivory)}}body.pipspool-page .field-tab.active:after{{content:"";position:absolute;left:0;right:0;bottom:-1px;height:3px;border-radius:3px 3px 0 0;background:var(--cyan);box-shadow:0 0 10px rgba(66,229,234,.35)}}.tab-count{{display:inline-flex;min-width:20px;height:20px;margin-left:6px;padding:0 6px;align-items:center;justify-content:center;border:1px solid #246fa9;border-radius:10px;background:#061a35;color:#a9bfd4;font-size:11px}}.field-tab.active .tab-count{{border-color:#2ca9c2;color:var(--cyan)}}
.field-workspace{{min-height:270px;padding:18px 4px 4px}}.field-panel[hidden]{{display:none}}.field-panel-heading{{display:flex;align-items:flex-start;justify-content:space-between;gap:18px;margin-bottom:15px;padding-bottom:12px;border-bottom:1px solid #174f80}}.field-panel-heading h3{{margin:0 0 3px;color:var(--ivory);font-size:15px}}.field-panel-heading p{{margin:0}}.group-actions{{display:flex;flex:0 0 auto;gap:7px}}.group-actions button{{padding:5px 10px;font-size:12px}}.choices{{display:grid;grid-template-columns:repeat(auto-fit,minmax(270px,1fr));gap:7px 18px}}.choice{{display:flex;align-items:center;gap:10px;min-height:34px;padding:5px 8px;border:1px solid transparent;border-radius:6px;color:#dce9f3}}.choice:hover{{border-color:#1767a8;background:#07284d}}.choice input{{flex:0 0 auto}}input[type=checkbox]{{accent-color:var(--orca-accent)}}
.field-footer{{display:flex;justify-content:space-between;align-items:center;margin-top:12px}}.danger-zone{{border-color:#704b47;background:linear-gradient(145deg,#352a29,#2a2222)}}.danger-zone p{{color:#ddbeb8}}.error{{color:var(--bad)}}
.page-footer{{margin-top:18px;padding:14px 10px 10px;border-top:1px solid #174f80;color:var(--orca-muted);font-size:11px;text-align:left}}.page-footer b{{color:var(--ivory);font-weight:650}}.footer-separator{{margin:0 7px;color:#3d7daf}}
.restart-banner{{grid-column:1/-1;display:flex;align-items:center;gap:10px;padding:12px 15px;border:1px solid var(--amber);border-radius:9px;background:#3a280d;color:#ffe4ad;font-weight:650;box-shadow:0 0 16px rgba(242,164,58,.14)}}.restart-banner[hidden]{{display:none}}.restart-symbol{{font-size:18px;color:var(--amber)}}
.sync-banner{{grid-column:1/-1;display:flex;align-items:center;gap:10px;padding:12px 15px;border:1px solid #42a9ff;border-radius:9px;background:#073354;color:#d8f6ff;font-weight:650;box-shadow:0 0 16px rgba(66,169,255,.12)}}.sync-banner[hidden]{{display:none}}.sync-symbol{{font-size:17px;color:var(--cyan)}}
.update-banner{{grid-column:1/-1;display:flex;align-items:center;gap:10px;padding:12px 15px;border:1px solid var(--cyan);border-radius:9px;background:#073354;color:#d8f6ff;font-weight:650;box-shadow:0 0 16px rgba(66,229,234,.12)}}.update-banner[hidden]{{display:none}}.update-symbol{{font-size:17px;color:var(--cyan)}}
@media(max-width:1100px){{.connection-layout{{grid-template-columns:1fr}}.gate-panel{{padding:17px 0 0;border-left:0;border-top:1px solid var(--orca-border)}}.spool-id-control{{top:12px}}.gate-grid{{grid-template-columns:repeat(4,minmax(108px,1fr))}}}}@media(max-width:850px){{.grid{{grid-template-columns:1fr}}.top-actions{{margin-left:0}}header{{flex-wrap:wrap}}.gate-panel>p{{padding-right:0;margin-top:58px}}.spool-id-control{{left:0;right:auto}}.gate-grid{{grid-template-columns:repeat(2,minmax(108px,1fr))}}}}
</style></head><body class="pipspool-page"><main>
<header><img class="logo" src="{PIPSPOOL_LOGO_DATA_URI}" alt="PipSpool"><div><h1>PipSpool</h1><p class="sub">Spoolman synchronization for OrcaSlicer</p></div><div class="top-actions"><button id="feedback">Feedback</button><button id="refresh">Refresh</button><button id="sync" class="primary">Synchronize now</button></div></header>
<div class="grid"><div id="updateBanner" class="update-banner"{"" if initial_available_update else " hidden"}><span class="update-symbol">↑</span><span id="updateText">PipSpool {escape(str(initial_available_update or ''))} is available — open File → Plugins to update.</span></div><div id="syncBanner" class="sync-banner"{"" if initial_synchronization_required and not initial_restart_required else " hidden"}><span class="sync-symbol">⇄</span><span>Spoolman changes detected — select Synchronize now to update Orca profiles.</span></div><div id="restartBanner" class="restart-banner"{"" if initial_restart_required else " hidden"}><span class="restart-symbol">↻</span><span>Filament profiles changed — restart OrcaSlicer to load them.</span></div><section class="card wide"><div class="connection-layout"><div class="connection-side"><h2>Connection</h2><div class="status-line"><img id="statusPip" class="status-pip" src="{initial_pip}" alt="Pip connection status"><div class="status-copy"><b id="status">{initial_status}</b><p id="connectionDetail" class="muted">{initial_detail}</p><p class="muted">Server settings, can be found in the PipSpool plugin settings.</p></div></div></div><div id="loadoutCard" class="gate-panel"><h2>Printer Gates/Toolheads</h2><p class="muted">A quick view of the gate assignments reported by Spoolman.</p><label class="spool-id-control" title="Add SET_SPOOL_ID to PipSpool filament profiles"><span class="spool-id-control-copy"><b>Spool ID G-code</b><span id="spoolIdState">{"Enabled" if initial_spool_id_gcode else "Disabled"}</span></span><span class="switch"><input id="spoolIdGcode" type="checkbox"{" checked" if initial_spool_id_gcode else ""}><span class="switch-track"></span></span></label><div id="loadout" class="gate-grid">{loadout_cards_html}</div><p id="loadoutEmpty" class="muted"{" hidden" if loadout_cards_html else ""}>No active spools are assigned to a printer gate in Spoolman.</p></div></div></section>
<section class="card"><h2>Active spools</h2><div class="toolbar"><input id="search" type="search" placeholder="Search by spool number, material, colour, manufacturer, name, location, gate or profile status"><details class="columns-menu"><summary>Columns</summary><div class="column-choices">{''.join(f'<label><input type="checkbox" data-table-column="{column}"{" checked" if column in initial_table_columns else ""}>{SPOOL_TABLE_COLUMN_LABELS[column]}</label>' for column in SPOOL_TABLE_COLUMNS)}</div></details></div><div class="spool-wrap"><table><thead><tr><th>Spool</th><th>Material</th><th data-column="filament">Filament</th><th data-column="manufacturer">Manufacturer</th><th data-column="colour">Colour</th><th data-column="nozzle">Nozzle</th><th data-column="bed">Bed</th><th data-column="remaining">Remaining</th><th data-column="location">Location</th><th data-column="loaded">Gate/Toolhead</th><th data-column="sync">Profile status</th></tr></thead><tbody id="spools">{spool_rows_html}</tbody></table></div><p id="empty" class="muted"{" hidden" if initial_spools else ""}>No matching active spools.</p></section>
<section class="card"><h2>Last synchronization</h2><div class="metrics"><div class="metric"><b id="active">{initial_active}</b><span>Active spools</span></div><div class="metric"><b id="changed">{initial_changed}</b><span>Changed spools</span></div><div class="metric"><b id="errors">{len(initial_errors) if isinstance(initial_report, dict) else '—'}</b><span>Errors</span></div></div><pre id="report" class="report">{escape(initial_report_text)}</pre></section>
<section class="card wide"><h2>Advanced field synchronization</h2><p class="muted">Choose settings from each Orca filament tab that PipSpool may expose in Spoolman. Ordinary spool details and temperatures are unaffected.</p><nav class="field-tabs" role="tablist" aria-label="Orca filament setting sections">{''.join(field_tabs)}</nav><div class="field-workspace">{''.join(field_panels)}</div><div class="field-footer"><span id="selectionCount" class="muted">{len(selected_fields)} field{"" if len(selected_fields) == 1 else "s"} selected</span><button id="saveFields">Save field selection</button></div></section>
<section class="card wide danger-zone"><h2>Cleanup</h2><p>Remove every unselected <code>orca_*</code> field from Spoolman. This permanently deletes the saved values in those fields for all filaments.</p><button id="cleanup">Remove unselected fields…</button></section></div>
<footer class="page-footer"><b>PipSpool {escape(PLUGIN_VERSION)}</b><span class="footer-separator">•</span>© {COPYRIGHT_YEAR} Donko<span class="footer-separator">•</span>Spoolman synchronization for OrcaSlicer<br><span>Independent community project; not affiliated with OrcaSlicer or Spoolman.</span></footer>
<script>
function byId(id){{return document.getElementById(id);}}
var state={{spools:[],busy:false,lowStockThreshold:{initial_low_stock_threshold},tableColumns:{json.dumps(initial_table_columns)}}};
var bridgeReady=false;
function send(action,extra){{
  if(bridgeReady&&window.orca){{
    var payload={{action:action}};
    var key;
    extra=extra||{{}};
    for(key in extra){{if(Object.prototype.hasOwnProperty.call(extra,key))payload[key]=extra[key];}}
    window.orca.postMessage(payload);
  }}else{{window.setTimeout(function(){{send(action,extra);}},150);}}
}}
function setBusy(value){{
  state.busy=value;
  var ids=['sync','refresh','saveFields','cleanup'];
  var i;
  for(i=0;i<ids.length;i++)byId(ids[i]).disabled=value;
}}
function selectedFields(){{
  var inputs=document.querySelectorAll('.choices input:checked');
  var values=[];
  var i;
  for(i=0;i<inputs.length;i++)values.push(inputs[i].value);
  return values;
}}
function updateCounts(){{
  var sections=document.querySelectorAll('.field-panel');
  var i;
  for(i=0;i<sections.length;i++){{
    var count=sections[i].querySelectorAll('input:checked').length;
    var group=sections[i].getAttribute('data-field-panel');
    var badge=document.querySelector('[data-tab-count="'+group+'"]');
    if(badge)badge.textContent=count;
  }}
  var total=selectedFields().length;
  byId('selectionCount').textContent=total+' field'+(total===1?'':'s')+' selected';
}}
function selectedTableColumns(){{
  var inputs=document.querySelectorAll('[data-table-column]:checked');
  var values=[];
  var i;
  for(i=0;i<inputs.length;i++)values.push(inputs[i].getAttribute('data-table-column'));
  return values;
}}
function applyTableColumns(){{
  var cells=document.querySelectorAll('[data-column]');
  var i;
  for(i=0;i<cells.length;i++)cells[i].style.display=state.tableColumns.indexOf(cells[i].getAttribute('data-column'))===-1?'none':'';
}}
function renderSpools(){{
  var q=byId('search').value.toLowerCase().replace(/^\s+|\s+$/g,'');
  var body=byId('spools');
  var count=0;
  var i,j;
  while(body.firstChild)body.removeChild(body.firstChild);
  for(i=0;i<state.spools.length;i++){{
    var spool=state.spools[i];
    if(JSON.stringify(spool).toLowerCase().indexOf(q)===-1)continue;
    count++;
    var row=document.createElement('tr');
    var loaded=spool.loaded&&spool.gate!=null?(spool.printer||'Printer')+' · Gate '+spool.gate:'—';
    var statusLabels={{synced:'Synced',profile_missing:'Profile missing',update_required:'Update required',error:'Error'}};
    var columns=['','', 'filament','manufacturer','colour','nozzle','bed','remaining','location','loaded','sync'];
    var values=['#'+spool.id,spool.material,spool.name,spool.vendor,'',spool.nozzle_temperature==null?'—':spool.nozzle_temperature+' °C',spool.bed_temperature==null?'—':spool.bed_temperature+' °C','',spool.location||'—',loaded,statusLabels[spool.sync_status]||'Unknown'];
    for(j=0;j<values.length;j++){{
      var cell=document.createElement('td');
      if(columns[j])cell.setAttribute('data-column',columns[j]);
      if(j===0){{
        var spoolLink=document.createElement('button');spoolLink.className='spool-link';spoolLink.setAttribute('data-open-spool',spool.id);spoolLink.title='Open this spool in Spoolman';spoolLink.textContent='#'+spool.id+' ↗';cell.appendChild(spoolLink);
      }}else if(j===4){{
        var swatch=document.createElement('span');
        swatch.className='swatch';
        swatch.style.background=spool.color;
        cell.appendChild(swatch);
        cell.appendChild(document.createTextNode(spool.color));
      }}else if(j===7){{
        var gauge=document.createElement('span');gauge.className='table-gauge';
        var fill=document.createElement('span');fill.className='table-gauge-fill';
        var step=spool.remaining_step==null?0:Math.max(0,Math.min(100,spool.remaining_step));
        var hue=Math.max(0,Math.min(120,(step-10)/90*120));fill.style.width=step+'%';fill.style.background=spool.remaining_step==null?'#31516d':'hsl('+hue+',46%,30%)';
        gauge.title=spool.remaining_percent==null?'Remaining percentage unavailable':spool.remaining_percent+'% remaining; gauge shown in 10% steps';
        var gaugeCopy=document.createElement('span');gaugeCopy.className='table-gauge-copy';gaugeCopy.textContent=spool.remaining==null?'—':spool.remaining+' g';gauge.appendChild(fill);gauge.appendChild(gaugeCopy);cell.appendChild(gauge);
      }}else if(j===10){{
        var profile=document.createElement('span');profile.className='profile-status profile-'+(spool.sync_status||'unknown');profile.textContent=values[j];profile.title=spool.sync_warning||'';cell.appendChild(profile);
      }}else{{cell.textContent=values[j];}}
      row.appendChild(cell);
    }}
    body.appendChild(row);
  }}
  applyTableColumns();
  byId('empty').style.display=count>0?'none':'block';
}}
function gateIconUri(color,gate,empty){{
  if(!/^#[0-9a-fA-F]{{6}}$/.test(color||''))color='#FFFFFF';
  var filament=empty?'#555b63':color;
  var svg='<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 72 58"><path d="M19 10h34l11 10v24l-8 8H16l-8-8V20z" fill="#292d33" stroke="#737983" stroke-width="3" stroke-linejoin="round"/><rect x="29" y="3" width="14" height="10" rx="4" fill="#181a1e" stroke="#858b94" stroke-width="2"/><path d="M36 5v44" fill="none" stroke="'+filament+'" stroke-width="5" stroke-linecap="round"/><path d="M26 25l5-7h10l5 7-3 10-7 4-7-4z" fill="#17191c" stroke="#969ca5" stroke-width="2"/><circle cx="36" cy="28" r="11" fill="#17191c" stroke="#969ca5" stroke-width="2"/><text x="36" y="33" text-anchor="middle" fill="#f2f3f5" font-family="Segoe UI,Arial,sans-serif" font-size="14" font-weight="700">'+gate+'</text><path d="M30 52h12l-3 5h-6z" fill="#17191c" stroke="#858b94" stroke-width="2" stroke-linejoin="round"/></svg>';
  return 'data:image/svg+xml;base64,'+window.btoa(svg);
}}
function renderLoadout(gates){{
  gates=gates||[];
  var body=byId('loadout');
  while(body.firstChild)body.removeChild(body.firstChild);
  var i;
  for(i=0;i<gates.length;i++){{
    var gate=gates[i];
    var empty=gate.empty===true;
    var low=!empty&&state.lowStockThreshold>0&&gate.remaining!=null&&gate.remaining<=state.lowStockThreshold;
    var problem=!empty&&!!gate.warning;
    var tile=document.createElement('article');tile.className='gate-tile'+(empty?' empty-gate':'')+(problem?' gate-problem':'');
    if(problem)tile.title=gate.warning;
    else if(low)tile.title='Low filament: '+gate.remaining+' g remaining (warning at '+state.lowStockThreshold+' g)';
    var status=document.createElement('span');status.className='gate-status';status.textContent=empty?'Empty':'Spool #'+gate.id;
    var image=document.createElement('img');image.className='gate-image';image.src=gateIconUri(gate.color,gate.gate,empty);image.alt='Gate '+gate.gate;
    var material=document.createElement('b');material.className='gate-material';material.textContent=empty?'—':(gate.material||'Unknown');
    var printer=document.createElement('span');printer.className='gate-printer';printer.textContent=gate.printer||'Printer';
    tile.appendChild(status);tile.appendChild(image);tile.appendChild(material);tile.appendChild(printer);
    if(!empty){{
      var gauge=document.createElement('span');gauge.className='gate-gauge';
      var fill=document.createElement('span');fill.className='gate-gauge-fill';
      var step=gate.remaining_step==null?0:Math.max(0,Math.min(100,gate.remaining_step));
      var hue=Math.max(0,Math.min(120,(step-10)/90*120));
      fill.style.width=step+'%';fill.style.background=gate.remaining_step==null?'#31516d':'hsl('+hue+',46%,30%)';
      gauge.title=gate.remaining_percent==null?'Remaining percentage unavailable':gate.remaining_percent+'% remaining; gauge shown in 10% steps';
      var copy=document.createElement('span');copy.className='gate-gauge-copy';
      if(low){{var lowLabel=document.createElement('span');lowLabel.className='gate-low-label';lowLabel.textContent='Low filament';copy.appendChild(lowLabel);}}
      var grams=document.createElement('span');grams.className='gate-grams';grams.textContent=gate.remaining==null?'— g':gate.remaining+' g';copy.appendChild(grams);
      gauge.appendChild(fill);gauge.appendChild(copy);tile.appendChild(gauge);
    }}
    body.appendChild(tile);
  }}
  byId('loadoutEmpty').style.display=gates.length?'none':'block';
}}
function applyState(data){{
  data=data||{{}};
  state.spools=data.spools||[];
  state.lowStockThreshold=data.low_stock_threshold==null?{DEFAULT_LOW_STOCK_THRESHOLD_GRAMS}:data.low_stock_threshold;
  state.tableColumns=data.spool_table_columns||state.tableColumns;
  var spoolIdEnabled=data.inject_spool_id_gcode!==false;
  byId('spoolIdGcode').checked=spoolIdEnabled;
  byId('spoolIdState').textContent=spoolIdEnabled?'Enabled':'Disabled';
  var columnInputs=document.querySelectorAll('[data-table-column]');
  var columnInputIndex;
  for(columnInputIndex=0;columnInputIndex<columnInputs.length;columnInputIndex++)columnInputs[columnInputIndex].checked=state.tableColumns.indexOf(columnInputs[columnInputIndex].getAttribute('data-table-column'))!==-1;
  var connected=data.connected===true;
  byId('status').textContent=connected?'Connection OK':'Not connected';
  byId('statusPip').src=connected?{json.dumps(PIP_HAPPY_DATA_URI)}:{json.dumps(PIP_SAD_DATA_URI)};
  byId('connectionDetail').textContent=data.detail||'';
  byId('connectionDetail').className='muted';
  byId('restartBanner').style.display=data.restart_required===true?'flex':'none';
  byId('syncBanner').style.display=data.synchronization_required===true&&data.restart_required!==true?'flex':'none';
  var availableUpdate=data.available_update||'';
  byId('updateBanner').style.display=availableUpdate?'flex':'none';
  byId('updateText').textContent=availableUpdate?('PipSpool '+availableUpdate+' is available — open File → Plugins to update.'):'';
  var report=data.last_report||null;
  byId('active').textContent=report?report.active_spools:state.spools.length;
  var changedSpools=0;
  if(report){{
    if(report.changed_spools!=null)changedSpools=report.changed_spools;
    else if(report.changes){{
      var changedIds={{}},changeIndex,changeMatch;
      for(changeIndex=0;changeIndex<report.changes.length;changeIndex++){{changeMatch=/^Spool #(\d+):/.exec(report.changes[changeIndex]);if(changeMatch)changedIds[changeMatch[1]]=true;}}
      changedSpools=Object.keys(changedIds).length;
    }}
  }}
  byId('changed').textContent=report?changedSpools:'—';
  byId('errors').textContent=report?(report.errors||[]).length:'—';
  if(report){{
    var reportText=changedSpools?(changedSpools+' spool profile'+(changedSpools===1?'':'s')+' changed.'):'No spool profiles needed changes.';
    if(report.changes&&report.changes.length)reportText+='\\n\\n• '+report.changes.join('\\n• ');
    if(report.errors&&report.errors.length)reportText+='\\n\\nErrors:\\n• '+report.errors.join('\\n• ');
    byId('report').textContent=reportText;
  }}else{{byId('report').textContent='No synchronization report yet.';}}
  var selected=data.selected_fields||[];
  var inputs=document.querySelectorAll('.choices input');
  var i;
  for(i=0;i<inputs.length;i++)inputs[i].checked=selected.indexOf(inputs[i].value)!==-1;
  updateCounts();
  renderSpools();
  renderLoadout(data.gates);
  setBusy(false);
}}
function hostMessage(data){{
  if(!data)return;
  if(data.type==='state'||data.type==='sync-result')applyState(data);
  else if(data.type==='error'){{setBusy(false);byId('connectionDetail').textContent=data.message;byId('connectionDetail').className='muted error';}}
  else if(data.type==='notice'){{setBusy(false);byId('connectionDetail').textContent=data.message;}}
}}
function startBridge(attempt){{
  attempt=attempt||0;
  if(window.orca&&typeof window.orca.postMessage==='function'&&typeof window.orca.onMessage==='function'){{
    bridgeReady=true;
    window.orca.onMessage(hostMessage);
    window.orca.postMessage({{action:'ready'}});
    return;
  }}
  if(attempt<100)window.setTimeout(function(){{startBridge(attempt+1);}},100);
  else{{byId('connectionDetail').textContent='Live controls unavailable in this Orca page.';byId('connectionDetail').className='muted error';}}
}}
byId('refresh').onclick=function(){{setBusy(true);send('refresh');}};
byId('feedback').onclick=function(){{send('feedback');}};
byId('sync').onclick=function(){{setBusy(true);send('sync',{{selected_fields:selectedFields()}});}};
byId('spoolIdGcode').onchange=function(){{
  var enabled=this.checked;
  byId('spoolIdState').textContent=enabled?'Enabled':'Disabled';
  send('save-spool-id-gcode',{{enabled:enabled}});
}};
byId('saveFields').onclick=function(){{setBusy(true);send('save-fields',{{selected_fields:selectedFields()}});}};
byId('cleanup').onclick=function(){{if(window.confirm('Permanently delete every unselected PipSpool field and its values from all Spoolman filaments?')){{setBusy(true);send('cleanup',{{selected_fields:selectedFields()}});}}}};
byId('search').oninput=renderSpools;
byId('spools').onclick=function(event){{
  var target=event.target;
  if(target&&target.getAttribute&&target.getAttribute('data-open-spool'))send('open-spool',{{spool_id:target.getAttribute('data-open-spool')}});
}};
var tableColumnInputs=document.querySelectorAll('[data-table-column]');
var tableColumnIndex;
for(tableColumnIndex=0;tableColumnIndex<tableColumnInputs.length;tableColumnIndex++)tableColumnInputs[tableColumnIndex].onchange=function(){{
  state.tableColumns=selectedTableColumns();
  applyTableColumns();
  send('save-columns',{{spool_table_columns:state.tableColumns}});
}};
var fieldInputs=document.querySelectorAll('.choices input');
var fieldIndex;
for(fieldIndex=0;fieldIndex<fieldInputs.length;fieldIndex++)fieldInputs[fieldIndex].onchange=updateCounts;
var fieldTabs=document.querySelectorAll('[data-field-tab]');
var fieldTabIndex;
for(fieldTabIndex=0;fieldTabIndex<fieldTabs.length;fieldTabIndex++)fieldTabs[fieldTabIndex].onclick=function(){{
  var group=this.getAttribute('data-field-tab');
  var tabIndex,panelIndex;
  for(tabIndex=0;tabIndex<fieldTabs.length;tabIndex++){{
    var selected=fieldTabs[tabIndex]===this;
    fieldTabs[tabIndex].classList.toggle('active',selected);
    fieldTabs[tabIndex].setAttribute('aria-selected',selected?'true':'false');
  }}
  var panels=document.querySelectorAll('[data-field-panel]');
  for(panelIndex=0;panelIndex<panels.length;panelIndex++){{
    var visible=panels[panelIndex].getAttribute('data-field-panel')===group;
    panels[panelIndex].classList.toggle('active',visible);
    panels[panelIndex].hidden=!visible;
  }}
}};
var groupButtons=document.querySelectorAll('[data-group-action]');
var groupIndex;
for(groupIndex=0;groupIndex<groupButtons.length;groupIndex++){{
  groupButtons[groupIndex].onclick=function(){{
    var inputs=this.parentNode.parentNode.querySelectorAll('input');
    var checked=this.getAttribute('data-group-action')==='all';
    var i;
    for(i=0;i<inputs.length;i++)inputs[i].checked=checked;
    updateCounts();
  }};
}}
applyState({initial_state_json});
startBridge();
</script></main></body></html>"""


PAGES_BASE = getattr(getattr(orca, "pages", None), "PagesPluginCapabilityBase", None)

if PAGES_BASE is not None:
    class PipSpoolPageCapability(PAGES_BASE):
        def __init__(self):
            super().__init__()

        def get_name(self):
            return "PipSpool"

        def get_ui(self):
            return pipspool_page_html(
                pipspool_page_state(friendly_initial_error=True)
            )

        def get_icon(self):
            try:
                if (
                    not PAGE_ICON_PATH.exists()
                    or PAGE_ICON_PATH.read_text(encoding="utf-8")
                    != PIPSPOOL_PAGE_ICON_SVG
                ):
                    PAGE_ICON_PATH.parent.mkdir(parents=True, exist_ok=True)
                    PAGE_ICON_PATH.write_text(
                        PIPSPOOL_PAGE_ICON_SVG, encoding="utf-8"
                    )
                return str(PAGE_ICON_PATH)
            except Exception as exc:
                log(f"[PAGE ICON ERROR] {exc}")
                return ""

        def _post_state(self, message_type="state", notice=None):
            payload = pipspool_page_state(notice)
            payload["type"] = message_type
            self.post_message(payload)

        def _post_initial_state(self):
            self._post_state()

        def _background(self, operation):
            def work():
                try:
                    notice = operation()
                    self._post_state("sync-result", notice)
                except Exception as exc:
                    log(f"[PAGE ERROR] {exc}")
                    self.post_message({"type": "error", "message": str(exc)})
            threading.Thread(target=work, daemon=True).start()

        def on_message(self, message):
            if not isinstance(message, dict):
                return
            action = message.get("action")
            if action == "ready":
                self._post_initial_state()
            elif action == "feedback":
                try:
                    if not webbrowser.open_new_tab(FEEDBACK_URL):
                        log("[FEEDBACK] The system browser did not accept the GitHub Issues URL.")
                except Exception as exc:
                    log(f"[FEEDBACK ERROR] {exc}")
            elif action == "open-spool":
                try:
                    spool_id = int(message.get("spool_id"))
                    if spool_id <= 0:
                        raise ValueError("Spool ID must be positive")
                    spoolman_url = normalize_url(
                        load_settings().get("spoolman_url", DEFAULT_SPOOLMAN_URL)
                    )
                    target = f"{spoolman_url}/?sel=spool:{spool_id}"
                    if not webbrowser.open_new_tab(target):
                        log(
                            "[OPEN SPOOL] The system browser did not accept "
                            f"the Spoolman URL for spool #{spool_id}."
                        )
                except (TypeError, ValueError) as exc:
                    log(f"[OPEN SPOOL ERROR] Invalid spool ID: {exc}")
                except Exception as exc:
                    log(f"[OPEN SPOOL ERROR] {exc}")
            elif action == "refresh":
                self._post_state()
            elif action == "save-fields":
                selected, _remove = parse_field_config({"selected_fields": message.get("selected_fields", [])})
                live_preset_values = host_filament_preset_snapshot(selected)
                def save_fields():
                    created, populated = save_advanced_field_selection(
                        selected, live_preset_values
                    )
                    detail = (
                        f" Filled Orca values for {populated} Spoolman filament(s)."
                        if populated else " All existing values were already populated."
                    )
                    return (
                        f"Saved {len(selected)} selected advanced field(s). "
                        f"Created {created} field(s)." + detail
                    )
                self._background(save_fields)
            elif action == "save-columns":
                columns = message.get("spool_table_columns")
                if not isinstance(columns, list):
                    columns = []
                selected_columns = [
                    column for column in SPOOL_TABLE_COLUMNS if column in columns
                ]
                save_settings({"spool_table_columns": selected_columns})
            elif action == "save-spool-id-gcode":
                enabled = message.get("enabled") is True
                save_settings({"inject_spool_id_gcode": enabled})
                notice = (
                    "Spool ID G-code enabled. Synchronize to update filament profiles."
                    if enabled else
                    "Spool ID G-code disabled. Synchronize to remove PipSpool's managed command."
                )
                self._post_state("state", notice)
            elif action == "sync":
                selected, _remove = parse_field_config({"selected_fields": message.get("selected_fields", [])})
                live_preset_values = host_filament_preset_snapshot(selected)
                def synchronize():
                    report, _spools = sync_with_spoolman(
                        selected, live_preset_values=live_preset_values
                    )
                    suffix = " Restart OrcaSlicer to load changed presets." if report.changed else ""
                    return "Synchronization completed." + suffix
                self._background(synchronize)
            elif action == "cleanup":
                def cleanup():
                    selected, _remove = parse_field_config({"selected_fields": message.get("selected_fields", [])})
                    save_settings({"selected_fields": list(selected)})
                    settings = load_settings()
                    removed = SpoolmanClient(settings["spoolman_url"]).remove_unselected_orca_filament_fields(selected)
                    return f"Removed {removed} unselected PipSpool field(s)."
                self._background(cleanup)


class SettingsCapability(orca.script.ScriptPluginCapabilityBase):
    def get_name(self):
        return "PipSpool Settings"

    def on_load(self):
        if not has_saved_settings():
            self._open_settings_window()

    def execute(self):
        self._open_settings_window()
        return orca.ExecutionResult.success("PipSpool settings opened")

    def _open_settings_window(self):
        current_settings = load_settings()
        current_url = current_settings.get("spoolman_url", DEFAULT_SPOOLMAN_URL)
        show_page = current_settings.get("show_pipspool_page", True) is not False
        current_low_stock_threshold = low_stock_threshold(current_settings)
        safe_current_url = escape(str(current_url), quote=True)
        safe_default_url = escape(DEFAULT_SPOOLMAN_URL, quote=True)
        show_page_checked = " checked" if show_page else ""
        safe_low_stock_threshold = escape(f"{current_low_stock_threshold:g}", quote=True)
        html = f"""<!doctype html>
<html><head><meta name="viewport" content="width=device-width,initial-scale=1"><style>
:root {{ color-scheme:dark; --page:#202124; --panel:#292a2d; --field:#1f2022;
  --line:#55585d; --text:#f1f3f4; --muted:#aeb4ba; --accent:#37c9da;
  --accent-hover:#51d6e5; }}
* {{ box-sizing:border-box; }}
body {{ margin:0; padding:28px; background:var(--page); color:var(--text);
  font:14px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif; }}
.header {{ display:flex; align-items:center; gap:16px; margin-bottom:20px; }}
.logo {{ width:64px; height:64px; flex:0 0 64px; object-fit:contain;
  filter:drop-shadow(0 4px 8px rgba(0,0,0,.28)); }}
h1 {{ margin:0; font-size:21px; line-height:1.15; }}
.subtitle {{ margin:4px 0 0; color:var(--muted); font-size:13px; }}
.card {{ padding:20px; border:1px solid #3d3f43; border-radius:12px; background:var(--panel); }}
.sync-card,.display-card {{ margin-top:12px; }}
.card-title {{ margin:0 0 5px; font-size:15px; font-weight:650; }}
.help {{ margin:0 0 17px; color:var(--muted); }}
label {{ display:block; margin-bottom:7px; font-weight:600; }}
input {{ width:100%; padding:11px 12px; border:1px solid var(--line); border-radius:7px;
  outline:none; background:var(--field); color:var(--text); font:inherit; }}
input:focus {{ border-color:var(--accent); box-shadow:0 0 0 2px rgba(55,201,218,.18); }}
.toggle {{ display:flex; align-items:flex-start; gap:11px; margin:13px 0 0; font-weight:400; cursor:pointer; }}
.toggle input {{ width:18px; height:18px; margin:2px 0 0; flex:0 0 18px; accent-color:var(--accent); }}
.toggle-copy {{ display:block; }}
.toggle-title {{ display:block; font-weight:650; }}
.toggle-help {{ display:block; margin-top:3px; color:var(--muted); font-size:12px; font-weight:400; }}
.example {{ margin-top:7px; color:var(--muted); font-size:12px; }}
.actions {{ display:flex; align-items:center; justify-content:space-between; gap:10px; margin-top:22px; }}
.right {{ display:flex; gap:9px; }}
button {{ min-height:36px; padding:8px 14px; border:1px solid var(--line); border-radius:7px;
  cursor:pointer; background:transparent; color:var(--text); font:600 13px system-ui,sans-serif; }}
button:hover {{ background:rgba(255,255,255,.06); }}
.primary {{ border-color:var(--accent); background:var(--accent); color:#102326; }}
.primary:hover {{ background:var(--accent-hover); }}
</style></head><body>
<div class="header"><img class="logo" src="{PIPSPOOL_LOGO_DATA_URI}" alt="PipSpool logo"><div><h1>PipSpool settings</h1>
<p class="subtitle">Connect OrcaSlicer to your Spoolman server</p></div></div>
<div class="card"><p class="card-title">Spoolman connection</p>
<p class="help">Enter the address you normally use to open Spoolman.</p>
<label for="url">Server address</label>
<input id="url" type="url" spellcheck="false" autocomplete="off"
 value="{safe_current_url}" placeholder="{safe_default_url}">
<div class="example">Include http:// or https:// and the port, if one is used.</div></div>
<div class="card sync-card"><p class="card-title">Filament setting ownership</p>
<p class="help">Orca supplies the initial values selected from its filament-setting tabs.
Blank Spoolman fields inherit from Orca; populated fields are preserved as overrides.</p>
<div class="example">Use “Reset Spoolman Filament Settings from Orca” only when you
want to replace all PipSpool-managed overrides for active filaments.</div></div>
<div class="card display-card"><p class="card-title">PipSpool page</p>
<p class="help">Choose whether PipSpool adds its dashboard to OrcaSlicer's top navigation.</p>
<label class="toggle" for="showPage"><input id="showPage" type="checkbox"{show_page_checked}>
<span class="toggle-copy"><span class="toggle-title">Show PipSpool page in OrcaSlicer</span>
<span class="toggle-help">Synchronization and plugin actions keep working when the page is hidden. Restart OrcaSlicer after changing this setting.</span></span></label></div>
<div class="card display-card"><p class="card-title">Low filament warning</p>
<p class="help">Highlight loaded gate/toolhead tiles when their remaining filament reaches this amount.</p>
<label for="lowStockThreshold">Warning threshold (grams)</label>
<input id="lowStockThreshold" type="number" min="0" step="1" value="{safe_low_stock_threshold}">
<div class="example">The default is 100 g. Set the threshold to 0 to disable low-stock warnings.</div></div>
<div class="actions"><button onclick="send('test')">Test connection</button>
<div class="right"><button onclick="send('cancel')">Cancel</button>
<button class="primary" onclick="send('save')">Save settings</button></div></div>
<script>
const url = document.getElementById('url');
const showPage = document.getElementById('showPage');
const lowStockThreshold = document.getElementById('lowStockThreshold');
function send(action) {{ window.orca.postMessage({{action:action,url:url.value,show_pipspool_page:showPage.checked,low_stock_threshold_grams:lowStockThreshold.value}}); }}
url.addEventListener('keydown', event => {{ if (event.key === 'Enter') send('save'); }});
</script>
</body></html>"""

        def on_message(data):
            if not isinstance(data, dict):
                return
            if data.get("action") == "cancel":
                window.close()
                return
            if data.get("action") == "test":
                try:
                    test_url = normalize_url(data.get("url", ""))
                except Exception as exc:
                    show_message(str(exc), title="Connection test", icon="error")
                    return

                def test_connection():
                    try:
                        spools = SpoolmanClient(test_url).active_spools()
                        show_message(
                            f"Connection successful.\n\nSpoolman returned {len(spools)} active spool(s).",
                            title="Connection test",
                        )
                    except Exception as exc:
                        log(f"[CONNECTION TEST ERROR] {exc}")
                        show_message(
                            f"Could not connect to Spoolman.\n\n{exc}",
                            title="Connection test",
                            icon="error",
                        )

                threading.Thread(target=test_connection, daemon=True).start()
                return
            if data.get("action") == "save":
                try:
                    updated_show_page = bool(data.get("show_pipspool_page", True))
                    visibility_changed = show_page != updated_show_page
                    updated_low_stock_threshold = numeric(
                        data.get("low_stock_threshold_grams")
                    )
                    if updated_low_stock_threshold is None or updated_low_stock_threshold < 0:
                        raise ValueError("Low-stock warning threshold must be 0 grams or more")
                    settings_update = {
                        "spoolman_url": data.get("url", ""),
                        "show_pipspool_page": updated_show_page,
                        "low_stock_threshold_grams": round(updated_low_stock_threshold, 1),
                    }
                    save_settings(settings_update)
                    window.close()
                    message = "PipSpool settings saved."
                    if visibility_changed:
                        message += "\n\nRestart OrcaSlicer to apply the page visibility change."
                    show_message(message)
                except Exception as exc:
                    show_message(str(exc), icon="error")

        window = orca.host.ui.create_window(
            html=html,
            title="PipSpool Settings",
            on_message=on_message,
        )


@orca.plugin
class PipSpoolPlugin(orca.base):
    def register_capabilities(self):
        if PAGES_BASE is not None and pipspool_page_enabled():
            orca.register_capability(PipSpoolPageCapability)
        orca.register_capability(SyncCapability)
        orca.register_capability(ResetFilamentSettingsCapability)
        orca.register_capability(LegacyCleanupCapability)
        orca.register_capability(SettingsCapability)
