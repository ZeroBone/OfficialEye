from queue import Queue
from threading import Thread
from typing import List, Union, Tuple

# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.error import OEError
from officialeye.error.errors.supervision import ErrSupervisionCorrespondenceNotFound
from officialeye.error.errors.template import ErrTemplateInvalidConcurrencyConfig
from officialeye.error.printing import oe_error_print_debug
from officialeye.supervision.result import SupervisionResult
from officialeye.template.template import Template
from officialeye.util.logger import oe_debug


class AnalysisWorker(Thread):

    def __init__(self, worker_id: int, queue: Queue, target: cv2.Mat, /):
        Thread.__init__(self)
        self.worker_id = worker_id
        self.queue = queue
        self._target = target
        self._results: List[Tuple[Union[SupervisionResult, None], Union[OEError, None]]] = []

    def run(self):

        while True:
            template = self.queue.get()

            try:
                _current_result = template.analyze(self._target)
                self._results.append((_current_result, None))
            except OEError as err:
                self._results.append((None, err))
            finally:
                self.queue.task_done()

    def get_successful_results(self):
        for result, error in self._results:
            if result is None or error is not None:
                continue
            yield result

    def get_errors(self):
        for _, error in self._results:
            if error is not None:
                yield error




def do_analyze(target: cv2.Mat, templates: List[Template], /, *, num_workers: int):

    if len(templates) == 0:
        # the program should be a noop if there are no templates provided
        return

    assert num_workers is not None

    if num_workers < 1:
        raise ErrTemplateInvalidConcurrencyConfig(
            "while setting up workers for analyzing the target image.",
            f"The provided number of workers ({num_workers}) cannot be less than one."
        )

    if num_workers > 0xff:
        raise ErrTemplateInvalidConcurrencyConfig(
            "while setting up workers for analyzing the target image.",
            f"The provided number of workers ({num_workers}) is too high."
        )

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

    # a list containing regular errors that occurred in workers
    regular_errors = []

    for worker in workers:
        for result in worker.get_successful_results():
            assert result is not None

            result_score = result.get_score()
            if result_score > best_result_score:
                best_result_score = result_score
                best_result = result

        for error in worker.get_errors():
            assert error is not None

            # we ignore regular errors here, because they may well be simply caused by trying to match
            # a given document against an invalid template, which is normal behavior
            if not error.is_regular:
                raise error
            else:
                oe_debug(f"Worker {worker.worker_id} returned the following non-regular error {error.code_text}:")
                oe_error_print_debug(error)
                regular_errors.append(error)

    # note: best_result may be None here

    if best_result is None:

        error = ErrSupervisionCorrespondenceNotFound(
            "while running supervisor",
            "could not establish correspondence of the image with any of the templates provided"
        )

        for worker_error in regular_errors:
            error.add_cause(worker_error)

        raise error

    oe_context().io_driver.output_supervision_result(target, best_result)
