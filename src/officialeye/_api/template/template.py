from __future__ import annotations

from typing import List, TYPE_CHECKING

import cv2

# noinspection PyProtectedMember
from officialeye._internal.context.singleton import initialize_internal_context
# noinspection PyProtectedMember
from officialeye._internal.template.schema.loader import load_template
# noinspection PyProtectedMember
from officialeye._internal.template.template_data import TemplateData
from officialeye._api.template.region import Keypoint, Feature


if TYPE_CHECKING:
    from officialeye._api.context import Context


def _load_template(template_path: str, /, **kwargs) -> TemplateData:

    initialize_internal_context(**kwargs)

    template = load_template(template_path)

    return template.get_template_data()


class Template:

    def __init__(self, context: Context, /, *, path: str):
        self._context = context
        self._path = path

        self._data: TemplateData | None = None

    # noinspection PyProtectedMember
    def load(self):
        """
        Loads the template into memory for further processing.

        If you prefer lazy-evaluation, do not call this method.
        Instead, run the desired operations with the template, and the necessary resources will be loaded on-the-fly.
        Use this method only if you really want to preload the template.
        """

        if self._data is not None:
            # data has already been loaded, nothing to do
            return

        future = self._context._submit_task(_load_template, "Loading template...", self._path)

        self._data = future.result()

        assert self._data is not None

    def get_image(self) -> cv2.Mat:
        self.load()
        return cv2.imread(self._data.source, cv2.IMREAD_COLOR)

    def get_mutated_image(self) -> cv2.Mat:
        img = self.get_image()
        return self._data.apply_source_mutators(img)

    @property
    def identifier(self) -> str:
        self.load()
        return self._data.identifier

    @property
    def name(self) -> str:
        self.load()
        return self._data.name

    @property
    def width(self) -> int:
        self.load()
        return self._data.width

    @property
    def height(self) -> int:
        self.load()
        return self._data.height

    @property
    def keypoints(self) -> List[Keypoint]:
        self.load()
        return self._data.keypoints

    @property
    def features(self) -> List[Feature]:
        self.load()
        return self._data.features
