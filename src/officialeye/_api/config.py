"""
Module for abstracting out the ability to inject custom configurations specified using dictionaries.
The goal of this module is to provide a nice API for validated user-specified configurations
and safely retrieving information from there.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Callable

from officialeye.error.errors.general import ErrInvalidKey

if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class Config(ABC):

    def __init__(self, config_dict: ConfigDict, /):
        self._config_dict = config_dict

    @abstractmethod
    def _get_invalid_key_error(self, key: str, /):
        raise NotImplementedError()

    def get(self, key: str, /, *, value_preprocessor: Callable[[str], any] | None = None, default=None):

        if key not in self._config_dict:

            if default is None:
                raise self._get_invalid_key_error(key)

            return default

        _value = self._config_dict[key]

        # apply value preprocessor
        if value_preprocessor is not None:
            _value = value_preprocessor(_value)

        return _value


class MutatorConfig(Config):

    def __init__(self, config_dict: ConfigDict, mutator_id: str, /):

        super().__init__(config_dict)

        self._mutator_id = mutator_id

    def _get_invalid_key_error(self, key: str, /):
        return ErrInvalidKey(
            f"while reading configuration of the '{self._mutator_id}' mutator.",
            f"Could not find a value for key '{key}'."
        )


class MatcherConfig(Config):

    def __init__(self, config_dict: ConfigDict, matcher_id: str, /):

        super().__init__(config_dict)

        self._matcher_id = matcher_id

    def _get_invalid_key_error(self, key: str, /):
        return ErrInvalidKey(
            f"while reading configuration of the '{self._matcher_id}' matcher.",
            f"Could not find a value for key '{key}'."
        )


class SupervisorConfig(Config):

    def __init__(self, config_dict: ConfigDict, matcher_id: str, /):

        super().__init__(config_dict)

        self._matcher_id = matcher_id

    def _get_invalid_key_error(self, key: str, /):
        return ErrInvalidKey(
            f"while reading configuration of the '{self._matcher_id}' supervisor.",
            f"Could not find a value for key '{key}'."
        )


class InterpretationConfig(Config):

    def __init__(self, config_dict: ConfigDict, interpretation_id: str, /):

        super().__init__(config_dict)

        self._interpretation_id = interpretation_id

    def _get_invalid_key_error(self, key: str, /):
        return ErrInvalidKey(
            f"while reading configuration of the '{self._interpretation_id}' interpretation.",
            f"Could not find a value for key '{key}'."
        )
