from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING


if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.context import Context


class IApiInterfaceImplementation(ABC):

    @abstractmethod
    def set_api_context(self, context: Context, /):
        """
        This method should be used to propagate the public API's context to the objects returned by the internal implementation of the API.
        Those objects are called 'external' and should be picklable if the API context has not yet been set via this method.
        If it was, then all methods guaranteed by the corresponding object's public API interface can be implemented properly.
        """
        raise NotImplementedError()
