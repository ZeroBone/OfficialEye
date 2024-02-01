import enum


class Verbosity(enum.IntEnum):
    QUIET = -1
    INFO = 0
    INFO_VERBOSE = 1
    DEBUG = 2
    DEBUG_VERBOSE = 3
