"""
Module for abstracting out the ability to inject custom configurations specified using dictionaries.
The goal of this module is to provide a nice API for validated user-specified configurations
and safely retrieving information from there.
"""

from abc import ABC, abstractmethod
from typing import Callable, Dict

from officialeye.error.errors.template import ErrTemplateInvalidMutator


class Config(ABC):

    # TODO: migrate from the Dict[str, any] to a more precise type (define in _types.py)
    def __init__(self, config_dict: Dict[str, any], /):
        self._config_dict = config_dict

        self._value_preprocessors: Dict[str, Callable[[str], any]] = {}

    def set_value_preprocessor(self, key: str, preprocessor: Callable[[str], any], /):
        self._value_preprocessors[key] = preprocessor

    @abstractmethod
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


class MutatorConfig(Config):

    def __init__(self, config_dict: Dict[str, any], mutator_id: str, /):

        super().__init__(config_dict)

        self._mutator_id = mutator_id

    def _get_invalid_key_error(self, key: str, /):
        return ErrTemplateInvalidMutator(
            f"while reading configuration of the '{self._mutator_id}' mutator.",
            f"Could not find a value for key '{key}'."
        )