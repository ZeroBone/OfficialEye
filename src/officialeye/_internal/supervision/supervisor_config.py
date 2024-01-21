from typing import Dict

from officialeye._internal.config.config import Config
from officialeye._internal.error.errors.supervision import ErrSupervisionInvalidEngineConfig


class SupervisorConfig(Config):

    def __init__(self, config_dict: Dict[str, any], supervision_engine_id: str, /):
        super().__init__(config_dict)

        self._supervision_engine_id = supervision_engine_id

    def _get_invalid_key_error(self, key: str, /):
        return ErrSupervisionInvalidEngineConfig(
            f"while reading configuration of the '{self._supervision_engine_id}' supervision engine.",
            f"Could not find a value for key '{key}'."
        )
