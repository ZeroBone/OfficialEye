from officialeye.context.singleton import oe_context
from officialeye.error.errors.io import ErrIOInvalidSupervisionEngine
from officialeye.io.driver import IODriver
from officialeye.io.drivers.ocr import OcrIODriver
from officialeye.io.drivers.std import StandardIODriver


_oe_io_driver = None


def oe_io_driver() -> IODriver:
    global _oe_io_driver

    assert oe_context().io_driver_id is not None, "Driver ID has not been set: context was not correctly initialized"

    if _oe_io_driver is not None:
        return _oe_io_driver

    # the IO driver is being loaded for the first time

    if oe_context().io_driver_id == StandardIODriver.DRIVER_ID:
        _oe_io_driver = StandardIODriver()
    if oe_context().io_driver_id == OcrIODriver.DRIVER_ID:
        _oe_io_driver = OcrIODriver()
    else:
        # unknown io driver specified
        raise ErrIOInvalidSupervisionEngine(
            f"while loading IO driver '{oe_context().io_driver_id}'",
            "The specified IO driver does not exist."
        )

    return _oe_io_driver
