from queue import Queue
from threading import Thread
from typing import List, Union

# noinspection PyPackageRequirements
import cv2

from officialeye.error.errors.supervision import ErrSupervisionCorrespondenceNotFound
from officialeye.io.driver_singleton import oe_io_driver
from officialeye.supervision.result import SupervisionResult
from officialeye.template.template import Template
from officialeye.util.logger import oe_debug


class AnalysisWorker(Thread):

    def __init__(self, worker_id: int, queue: Queue, target: cv2.Mat, /):
        Thread.__init__(self)
        self.worker_id = worker_id
        self.queue = queue
        self._target = target
        self._result = None

    def run(self):

        while True:
            template = self.queue.get()

            try:
                self._result = template.analyze(self._target)
            finally:
                self.queue.task_done()

    def get_result(self) -> Union[SupervisionResult, None]:
        return self._result


def _handle_analysis_result(target: cv2.Mat, result: Union[SupervisionResult, None], /):

    if result is None:
        raise ErrSupervisionCorrespondenceNotFound(
            "while running supervisor",
            "could not establish correspondence of the image with any of the templates provided"
        )

    oe_io_driver().output_analyze_result(target, result)


def do_analyze(target: cv2.Mat, templates: List[Template], /, *, num_workers: int):

    if len(templates) == 0:
        # the program should be a noop if there are no templates provided
        return

    assert num_workers is not None
    assert num_workers >= 1
    assert num_workers <= 0xff

    queue = Queue(maxsize=len(templates))

    workers = [AnalysisWorker(worker_id, queue, target) for worker_id in range(num_workers)]

    for worker in workers:
        worker.daemon = True
        worker.start()

    for template in templates:
        queue.put(template)

    queue.join()

    best_result = None
    best_result_score = -1.0

    for worker in workers:
        result = worker.get_result()

        if result is None:
            oe_debug(f"Worker {worker.worker_id} has provided no result (return value = none).")
            continue

        result_score = result.get_score()
        if result_score > best_result_score:
            best_result_score = result_score
            best_result = result

    # note: best_result may be None here
    _handle_analysis_result(target, best_result)
