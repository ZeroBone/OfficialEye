import time
from typing import Tuple


class Timer:

    def __init__(self):
        self._start_time: Tuple[float, float] | None = None
        self._end_time: Tuple[float, float] | None = None

    def __enter__(self):
        self._start_time = time.perf_counter(), time.process_time()

    def __exit__(self, exc_type, exc_val, exc_tb):
        self._end_time = time.perf_counter(), time.process_time()

    def get_real_time(self) -> float:
        assert self._start_time is not None
        assert self._end_time is not None
        return self._end_time[0] - self._start_time[0]

    def get_cpu_time(self) -> float:
        assert self._start_time is not None
        assert self._end_time is not None
        return self._end_time[1] - self._start_time[1]
