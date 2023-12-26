from officialeye.context.singleton import oe_context
from officialeye.io.driver import IODriver
from officialeye.io.drivers.std import StandardIODriver
from officialeye.utils.logger import print_error

_oe_io_driver = None


def oe_io_driver() -> IODriver:
    global _oe_io_driver

    assert oe_context().io_driver_id is not None, "Driver ID has not been set: context was not correctly initialized"

    if _oe_io_driver is not None:
        return _oe_io_driver

    # the IO driver is being loaded for the first time

    if oe_context().io_driver_id == StandardIODriver.DRIVER_ID:
        _oe_io_driver = StandardIODriver()
    else:
        # unknown io driver specified
        print_error(f"while loading IO driver '{oe_context().io_driver_id}'", "The specified IO driver does not exist.")
        exit(38)

    return _oe_io_driver
