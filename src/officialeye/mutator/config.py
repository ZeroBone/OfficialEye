from typing import Dict

from officialeye.config import Config
from officialeye.error.errors.template import ErrTemplateInvalidMutator


class MutatorConfig(Config):

    def __init__(self, config_dict: Dict[str, any], mutator_id: str, /):

        super().__init__(config_dict)

        self._mutator_id = mutator_id

    def _get_invalid_key_error(self, key: str, /):
        return ErrTemplateInvalidMutator(
            f"while reading configuration of the '{self._mutator_id}' mutator.",
            f"Could not find a value for key '{key}'."
        )
