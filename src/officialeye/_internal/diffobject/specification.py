from typing import Dict

import strictyaml as yml

from officialeye._internal.diffobject.specification_entry import DiffObjectSpecificationEntry


class DiffObjectSpecification:
    """
    Class representing a complete specification of an object that supports partial definitions and difference application.
    """

    def __init__(self, specification: Dict[str, any], /, *, validate_specification: bool = True):
        self._spec = specification
        if validate_specification:
            self._validate_spec()

    def get_spec_as_dict(self) -> Dict[str, any]:
        return self._spec

    def _validate_spec(self, /):

        def _validator(entry_point: Dict[str, any], /):
            for key in entry_point:
                assert isinstance(key, str)

                value = entry_point[key]

                if isinstance(value, DiffObjectSpecificationEntry):
                    continue

                if isinstance(value, dict):
                    _validator(value)
                    continue

                assert False

        _validator(self._spec)

    def get_schema(self) -> yml.Validator:

        def _mapper(entry_point: Dict[str, any], /) -> yml.Validator:

            mapped_dict = {}
            assert isinstance(entry_point, dict)

            for key in entry_point:
                assert isinstance(key, str)
                value = entry_point[key]

                if isinstance(value, DiffObjectSpecificationEntry):

                    # the value might be provided explicitly
                    mapped_dict[yml.Optional(key)] = value.get_schema()

                    # or it can be obtained from a previous value by applying a difference strategy
                    mapped_dict[yml.Optional("$" + key)] = yml.Str()

                    continue

                if isinstance(value, dict):
                    mapped_dict[yml.Optional(key)] = _mapper(value)
                    continue

                assert False

            return yml.Map(mapped_dict)

        return _mapper(self._spec)
