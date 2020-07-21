# A simple "top_pkg"

This is an Ibex-specific "top_pkg" that contains constants used by DV
code vendored from OpenTitan. These constants are things like the
address width of the main bus.

Since we don't want to have to vendor in the global constants from
OpenTitan, which change from time to time and contain information
about flash memory layout (completely irrelevant to Ibex), we have a
special `ibex_top_pkg` and our vendoring system patches OpenTitan DV
code to require that instead of `top_pkg` (reserved for the OpenTitan
version).
