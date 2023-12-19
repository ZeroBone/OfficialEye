from typing import List

from officialeye.debug.container import DebugContainer
from officialeye.match.result import KeypointMatchingResult
from officialeye.supervision.result import SupervisionResult
from officialeye.supervision.supervisor import Supervisor


class CombinatorialSupervisor(Supervisor):

    ENGINE_ID = "combinatorial"

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, /, *, debug: DebugContainer = None):
        super().__init__(template_id, kmr, debug=debug)

    def _run(self) -> List[SupervisionResult]:
        return []
