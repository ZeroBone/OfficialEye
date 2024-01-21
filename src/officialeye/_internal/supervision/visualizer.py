from typing import List

import cv2
import numpy as np

from officialeye._internal.context.context import Context
from officialeye._internal.supervision.result import SupervisionResult
from officialeye._internal.template.region.keypoint import TemplateKeypoint


class SupervisionResultVisualizer:

    def __init__(self, context: Context, result: SupervisionResult, target: cv2.Mat):
        self._context = context
        self._result = result
        self._target = target

        # sorting is important, because we will be traversing the list multiple times
        # and the code relies on the identity of traverse orders
        self._relevant_keypoint_ids: List[str] = sorted(result.get_relevant_keypoint_ids())

        self._palette_width = max(self.get_template().get_keypoint(keypoint_id).w
                                  for keypoint_id in self._relevant_keypoint_ids)

    def get_template(self):
        return self._context.get_template(self._result.template_id)

    def get_padded_keypoint_image(self, keypoint: TemplateKeypoint) -> np.ndarray:

        assert keypoint.w <= self._palette_width

        keypoint_image = keypoint.to_image()

        padding_width = self._palette_width - keypoint.w
        assert padding_width >= 0

        if keypoint.w == self._palette_width:
            return keypoint_image

        assert padding_width > 0

        """
        white_pixel = np.array([[[0xff, 0xff, 0xff]]], dtype=keypoint_image.dtype)
        vertical_bar = np.repeat(white_pixel, keypoint.h, axis=0)
        padding = np.repeat(vertical_bar, padding_width, axis=1)
        """

        padding = np.full((keypoint.h, padding_width, 3), 0xff, dtype=np.uint8)
        keypoint_padded = np.concatenate((padding, keypoint_image), axis=1)

        assert keypoint_padded.shape[0] == keypoint.h
        assert keypoint_padded.shape[1] == self._palette_width

        return keypoint_padded

    def render(self) -> cv2.Mat:

        keypoints_palette = cv2.vconcat([
            self.get_padded_keypoint_image(self.get_template().get_keypoint(keypoint_id))
            for keypoint_id in self._relevant_keypoint_ids
        ])

        assert keypoints_palette.shape[1] == self._palette_width

        if keypoints_palette.shape[0] > self._target.shape[0]:
            # the height of the palette is greater than the height of the target image.
            # we pad the target image from below, to ensure that the height is at least the height of the palette
            padding_height = keypoints_palette.shape[0] - self._target.shape[0]
            padding = np.full((padding_height, self._target.shape[1], 3), 0xff, dtype=np.uint8)
            img = np.concatenate((self._target, padding), axis=0)
        else:
            img = self._target.copy()

        if keypoints_palette.shape[0] < self._target.shape[0]:
            # the height of the palette is less than the height of the target image
            # pad the palette from below, to ensure that the height is at least the height of the target image
            padding_height = self._target.shape[0] - keypoints_palette.shape[0]
            padding = np.full((padding_height, keypoints_palette.shape[1], 3), 0xff, dtype=np.uint8)
            keypoints_palette = np.concatenate((keypoints_palette, padding), axis=0)

        visualization = cv2.hconcat([keypoints_palette, img])

        for match in self._result.get_keypoint_matching_result().get_matches():
            # compute the location of the match in the palette part of the visualization
            match_palette_location = match.get_template_point()

            _padding_width = self._palette_width - self.get_template().get_keypoint(match.keypoint_id).w
            match_palette_location[0] += _padding_width

            for keypoint_id in self._relevant_keypoint_ids:
                if keypoint_id == match.keypoint_id:
                    break
                # in the palette, there is a keypoint above the keypoint corresponding to the current match.
                # therefore, we need to adjust the palette location.
                match_palette_location[1] += self.get_template().get_keypoint(keypoint_id).h

            # compute the location of the match in the target image part of the visualization
            match_target_location = match.get_target_point()
            match_target_location[0] += self._palette_width

            # draw a line visualizing the match
            # TODO: make this depend on the weight of the match
            if True:  # FIXME
                match_color = (0, 0xff, 0)  # green
            else:
                match_color = (0, 0, 0xff)  # red

            visualization = cv2.line(visualization, match_palette_location, match_target_location, match_color, 2)

        return visualization
