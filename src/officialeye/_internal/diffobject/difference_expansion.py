from typing import Dict

from officialeye._internal.diffobject.difference_modes import DIFF_MODE_OVERRIDE, DIFF_MODE_ADD, DIFF_MODE_REMOVE
from officialeye._internal.diffobject.exception import DiffObjectException
from officialeye._internal.diffobject.specification import DiffObjectSpecification
from officialeye._internal.diffobject.specification_entry import DiffObjectSpecificationEntry
from officialeye._internal.logger.singleton import get_logger


class DiffObjectExpansion:
    """
    This class maintains a state capturing the information gathered by applying partial objects of the same type in sequence.
    That is, this class allows you to build a complete specification-compliant object out of a sequence of partial objects,
    by applying the difference specifications contained in the partial objects appropriately.
    """

    def __init__(self, spec: DiffObjectSpecification, /):
        self._spec = spec
        self._cur_object = {}

    def add(self, partial_object: Dict[str, any], /):
        """
        Changes the current object by using the information from the given object.

        Arguments:
            partial_object: Which object to get the information from.

        Raises:
            DiffObjectException: In the event of a merge error.
        """

        def _do_add(specification_dict: Dict[str, any],
                    current_dict: Dict[str, any],
                    object_dict: Dict[str, any], /, *, previous_keys: str = ""):
            """
            Arguments:
                specification_dict: Current subdictionary of the specification represented as a dictionary
                current_dict: Corresponding subdictionary of `self._cur_object`
                object_dict: Corresponding subdictionary of `partial_object`
            """

            assert isinstance(specification_dict, dict)
            assert isinstance(current_dict, dict)
            assert isinstance(object_dict, dict)

            for key in specification_dict:

                if key not in object_dict:
                    # the current key is not present in the partial object at all
                    # hence, there is nothing to do
                    continue

                specification_entry = specification_dict[key]
                current_value = current_dict[key] if key in current_dict else None  # corresponding value in `self._cur_object`
                object_value = object_dict[key]  # corresponding value in `partial_object`
                object_value_diff_mode = object_dict[f"${key}"] if f"${key}" in object_dict else None

                full_key = f"{previous_keys}{key}"

                get_logger().debug_verbose(f"Key: '{full_key}' Specification value: {specification_entry} "
                                           f"Object value: {object_value} Current value: {current_value}")

                if isinstance(specification_entry, dict):
                    # the specification says that there is a nested dictionary at the present key.
                    # therefore, we need to recursively apply the diffs
                    if current_value is not None:
                        new_current_dict = current_value
                    else:
                        new_current_dict = {}
                        current_dict[key] = new_current_dict

                    _do_add(specification_entry, new_current_dict, object_value, previous_keys=f"{previous_keys}{key}.")
                    continue

                # handle non-recursive cases
                assert isinstance(specification_entry, DiffObjectSpecificationEntry)

                # test whether the partial object contains an entry explicitly specifying a difference node
                if object_value_diff_mode is not None:
                    if object_value_diff_mode not in (
                        DIFF_MODE_OVERRIDE,
                        DIFF_MODE_ADD,
                        DIFF_MODE_REMOVE
                    ):
                        raise DiffObjectException(f"Unknown difference mode specification '{object_value_diff_mode}' for key '{full_key}'.")
                    diff_mode = object_value_diff_mode
                else:
                    # default difference mode
                    diff_mode = DIFF_MODE_OVERRIDE

                current_dict[key] = specification_entry.apply_diff(current_value, object_value, diff_mode)

        _do_add(
            self._spec.get_spec_as_dict(),
            self._cur_object,
            partial_object
        )

    def get_current_partial_object(self) -> Dict[str, any]:
        return self._cur_object.copy()

    def get_full_object(self) -> Dict[str, any]:
        """
        Retrieves the full object with all the differences applied.

        Raises:
            DiffObjectException: If there is not enough information to build the entire object (i.e., not all keys are present).
        """

        def _verify_object_completeness(cur_obj_dict: Dict[str, any], spec_dict: Dict[str, any], /, *, previous_keys: str = ""):

            for key in spec_dict:
                spec_entry = spec_dict[key]

                full_key = f"{previous_keys}{key}"

                if key not in cur_obj_dict:
                    raise DiffObjectException(f"Could not resolve value for key '{full_key}'.")

                cur_obj_value = cur_obj_dict[key]

                if isinstance(spec_entry, dict):
                    # completeness should be checked recursively
                    assert isinstance(cur_obj_value, dict)
                    _verify_object_completeness(cur_obj_value, spec_entry, previous_keys=f"{previous_keys}{key}.")
                    continue

                assert isinstance(spec_entry, DiffObjectSpecificationEntry)

        _verify_object_completeness(self._cur_object, self._spec.get_spec_as_dict())

        return self._cur_object.copy()
