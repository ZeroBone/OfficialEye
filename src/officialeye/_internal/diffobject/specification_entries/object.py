from typing import Union

import strictyaml as yml

from officialeye._internal.diffobject.difference_modes import DIFF_MODE_OVERRIDE, DIFF_MODE_ADD, DIFF_MODE_REMOVE
from officialeye._internal.diffobject.exception import DiffObjectException
from officialeye._internal.diffobject.specification_entry import DiffObjectSpecificationEntry


class ObjectSpecificationEntry(DiffObjectSpecificationEntry):

    def __init__(self, validator: yml.Validator, /):
        super().__init__(validator)

    def apply_diff(self, current_value: Union[dict, None], diff_value: dict, diff_mode: str) -> dict:
        assert current_value is None or isinstance(current_value, dict)
        assert isinstance(diff_value, dict)

        if diff_mode == DIFF_MODE_OVERRIDE:
            return diff_value

        if current_value is None:
            raise DiffObjectException(f"Could not apply difference mode '{diff_mode}' because the previous value is not available.")

        if diff_mode == DIFF_MODE_ADD:
            # merge the two dictionaries while prioritizing the `diff_value` entries
            return {**current_value, **diff_value}

        if diff_mode == DIFF_MODE_REMOVE:
            new_value = {}
            for key in current_value:
                if key in diff_value:
                    continue
                new_value[key] = current_value[key]
            return new_value

        raise DiffObjectException(f"The list type is incompatible with difference mode specification '{diff_mode}'.")
