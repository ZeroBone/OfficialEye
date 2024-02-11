from __future__ import annotations

from abc import ABC
from typing import TYPE_CHECKING, Dict

# noinspection PyProtectedMember
from officialeye._api.template.region import IRegion
from officialeye._internal.context.singleton import get_internal_context

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.template.template_interface import ITemplate
    from officialeye._internal.template.external_template import ExternalTemplate
    from officialeye._internal.template.internal_template import InternalTemplate


class SharedRegion(IRegion, ABC):

    def __init__(self, /, *, identifier: str, x: int, y: int, w: int, h: int):
        self._identifier = identifier
        self._x = x
        self._y = y
        self._w = w
        self._h = h

    @property
    def identifier(self) -> str:
        return self._identifier

    @property
    def x(self) -> int:
        return self._x

    @property
    def y(self) -> int:
        return self._y

    @property
    def w(self) -> int:
        return self._w

    @property
    def h(self) -> int:
        return self._h


class InternalRegion(SharedRegion, ABC):

    def __init__(self, template_id: str, region_dict: Dict[str, any], /):
        super().__init__(
            identifier=str(region_dict["id"]),
            x=int(region_dict["x"]),
            y=int(region_dict["y"]),
            w=int(region_dict["w"]),
            h=int(region_dict["h"])
        )

        self._template_id = template_id

    @property
    def template(self) -> InternalTemplate:
        return get_internal_context().get_template(self._template_id)


class ExternalRegion(SharedRegion, ABC):

    def __init__(self, internal_region: InternalRegion, external_template: ExternalTemplate, /):
        super().__init__(
            identifier=internal_region.identifier,
            x=internal_region.x,
            y=internal_region.y,
            w=internal_region.w,
            h=internal_region.h
        )

        self._external_template = external_template

    @property
    def template(self) -> ITemplate:
        return self._external_template
