import abc
from typing import Dict, Callable


class Config(abc.ABC):

    def __init__(self, config_dict: Dict[str, any], /):
        self._config_dict = config_dict

        self._value_preprocessors: Dict[str, Callable[[str], any]] = {}

    def set_value_preprocessor(self, key: str, preprocessor: Callable[[str], any], /):
        self._value_preprocessors[key] = preprocessor

    @abc.abstractmethod
    def _get_invalid_key_error(self, key: str, /):
        raise NotImplementedError()

    def get(self, key: str, /, *, default=None):

        if key not in self._config_dict:

            if default is None:
                raise self._get_invalid_key_error(key)

            return default

        _value = self._config_dict[key]

        # apply value preprocessor
        if key in self._value_preprocessors:
            _value = self._value_preprocessors[key](_value)

        return _value
