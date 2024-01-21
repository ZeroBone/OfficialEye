import abc
from abc import ABC

import strictyaml as yml


class DiffObjectSpecificationEntry(ABC):

    def __init__(self, validator: yml.Validator, /):
        self._validator = validator

    def get_schema(self) -> yml.Validator:
        """ Retrieves a schema for the current specification entry. """
        return self._validator

    @abc.abstractmethod
    def apply_diff(self, current_value: any, diff_value: any, diff_mode: str) -> any:
        """
        Calculates a new value for an entry, based on currently available value, some provided value, and a way of combining them.

        Arguments:
            current_value: The current value assigned to the entry, or None if there is no such value.
            diff_value: A new value provided for this entry.
            diff_mode: How the two values are to be combined to form a new value.

        Returns:
            The new value obtained by combining current_value with diff_value using diff_mode.

        Raises:
            DiffObjectException: If the difference mode cannot be applied to the present entry, for example, due to its type.
        """
        raise NotImplementedError()
