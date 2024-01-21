from typing import Union

import strictyaml as yml

from officialeye._internal.diffobject.difference_modes import DIFF_MODE_OVERRIDE, DIFF_MODE_ADD
from officialeye._internal.diffobject.exception import DiffObjectException
from officialeye._internal.diffobject.specification_entry import DiffObjectSpecificationEntry


class ListSpecificationEntry(DiffObjectSpecificationEntry):

    def __init__(self, validator: yml.Validator, /):
        super().__init__(validator)

    def apply_diff(self, current_value: Union[list, None], diff_value: list, diff_mode: str) -> list:
        assert current_value is None or isinstance(current_value, list)
        assert isinstance(diff_value, list)

        if diff_mode == DIFF_MODE_OVERRIDE:
            return diff_value

        if current_value is None:
            raise DiffObjectException(f"Could not apply difference mode '{diff_mode}' because the previous value is not available.")

        if diff_mode == DIFF_MODE_ADD:
            return current_value + diff_value

        raise DiffObjectException(f"The list type is incompatible with difference mode specification '{diff_mode}'.")
