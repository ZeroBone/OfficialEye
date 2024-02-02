from abc import ABC, abstractmethod


class AnalysisResult(ABC):

    @abstractmethod
    def get_score(self) -> float:
        raise NotImplementedError()
