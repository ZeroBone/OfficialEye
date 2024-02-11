from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.context import Context


class IApiInterfaceImplementation(ABC):

    @abstractmethod
    def set_api_context(self, context: Context, /) -> None:
        """
        This method should be used to propagate the public API's context to the objects returned by the internal implementation of the API.
        Those objects are called 'external' and should be picklable if the API context has not yet been set via this method.
        If it was, then all methods guaranteed by the corresponding object's public API interface can be implemented properly.
        """
        raise NotImplementedError()

    @abstractmethod
    def clear_api_context(self) -> None:
        """
        This method should clear the public API's context stored in the current object, and in all internal objects implementing this interface.
        It is essential that after running this method, the object is picklable.
        """
        raise NotImplementedError()
