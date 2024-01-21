from typing import Dict

from officialeye._internal.config.config import Config
from officialeye._internal.error.errors.matching import ErrMatchingInvalidEngineConfig


class KeypointMatcherConfig(Config):

    def __init__(self, config_dict: Dict[str, any], matching_engine_id: str, /):
        super().__init__(config_dict)

        self._matching_engine_id = matching_engine_id

    def _get_invalid_key_error(self, key: str, /):
        return ErrMatchingInvalidEngineConfig(
            f"while reading configuration of the '{self._matching_engine_id}' matching engine.",
            f"Could not find a value for key '{key}'."
        )
