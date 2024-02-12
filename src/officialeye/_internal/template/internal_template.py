from __future__ import annotations

import os
import random
from typing import TYPE_CHECKING, Dict, Iterable, List

import numpy as np

# noinspection PyProtectedMember
from officialeye._api.future import Future

# noinspection PyProtectedMember
from officialeye._api.image import IImage

# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch

# noinspection PyProtectedMember
from officialeye._api.template.supervisor import ISupervisor

# noinspection PyProtectedMember
from officialeye._api.template.template import ITemplate
from officialeye._internal.context.singleton import get_internal_afi, get_internal_context

# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity
from officialeye._internal.template.feature_class.loader import load_template_feature_classes
from officialeye._internal.template.feature_class.manager import FeatureClassManager
from officialeye._internal.template.image import InternalImage
from officialeye._internal.template.internal_feature import InternalFeature
from officialeye._internal.template.internal_matching_result import InternalMatchingResult
from officialeye._internal.template.internal_supervision_result import InternalSupervisionResult
from officialeye._internal.template.keypoint import InternalKeypoint
from officialeye._internal.template.utils import load_mutator_from_dict
from officialeye._internal.timer import Timer
from officialeye.error.errors.general import ErrInvalidIdentifier, ErrOperationNotSupported
from officialeye.error.errors.supervision import ErrSupervisionCorrespondenceNotFound
from officialeye.error.errors.template import ErrTemplateInvalidFeature, ErrTemplateInvalidKeypoint

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.mutator import IMutator

    # noinspection PyProtectedMember
    from officialeye._api.template.matcher import IMatcher

    # noinspection PyProtectedMember
    from officialeye._api.template.supervision_result import ISupervisionResult
    from officialeye.types import ConfigDict


# TODO: refactor this into an enum
_SUPERVISION_RESULT_FIRST = "first"
_SUPERVISION_RESULT_RANDOM = "random"
_SUPERVISION_RESULT_BEST_MSE = "best_mse"
_SUPERVISION_RESULT_BEST_SCORE = "best_score"


class InternalTemplate(ITemplate):

    def __init__(self, yaml_dict: Dict[str, any], path_to_template: str, /):
        super().__init__()

        self._path_to_template = path_to_template

        self._template_id = yaml_dict["id"]
        self._name = yaml_dict["name"]
        self._source = yaml_dict["source"]

        self._height, self._width, _ = self.get_image().load().shape

        self._source_mutators: List[IMutator] = [
            load_mutator_from_dict(mutator_dict) for mutator_dict in yaml_dict["mutators"]["source"]
        ]

        self._target_mutators: List[IMutator] = [
            load_mutator_from_dict(mutator_dict) for mutator_dict in yaml_dict["mutators"]["target"]
        ]

        self._keypoints: Dict[str, InternalKeypoint] = {}
        self._features: Dict[str, InternalFeature] = {}

        for keypoint_id in yaml_dict["keypoints"]:
            keypoint_dict = yaml_dict["keypoints"][keypoint_id]
            keypoint_dict["id"] = keypoint_id
            keypoint = InternalKeypoint(self.identifier, keypoint_dict)

            if keypoint.identifier in self._keypoints:
                raise ErrTemplateInvalidKeypoint(
                    f"while initializing keypoint '{keypoint_id}' of template '{self.identifier}'",
                    f"There is already a keypoint with the same identifier '{keypoint.identifier}'."
                )

            if keypoint.identifier in self._features:
                raise ErrTemplateInvalidKeypoint(
                    f"while initializing keypoint '{keypoint_id}' of template '{self.identifier}'",
                    f"There is already a feature with the same identifier '{keypoint.identifier}'."
                )

            self._keypoints[keypoint.identifier] = keypoint

        self._matching = yaml_dict["matching"]
        self._supervision = yaml_dict["supervision"]

        # load feature classes
        self._feature_class_manager = load_template_feature_classes(yaml_dict["feature_classes"], self.identifier)

        # load features
        for feature_id in yaml_dict["features"]:
            feature_dict = yaml_dict["features"][feature_id]
            feature_dict["id"] = feature_id
            feature = InternalFeature(self.identifier, feature_dict)

            if feature.identifier in self._keypoints:
                raise ErrTemplateInvalidFeature(
                    f"while initializing feature '{feature_id}' of template '{self.identifier}'",
                    f"There is already a keypoint with the same identifier '{feature.identifier}'."
                )

            if feature.identifier in self._features:
                raise ErrTemplateInvalidFeature(
                    f"while initializing feature '{feature_id}' of template '{self.identifier}'",
                    f"There is already a feature with the same identifier '{feature.identifier}'."
                )

            self._features[feature.identifier] = feature

        get_internal_context().add_template(self)

    def get_source_mutators(self) -> Iterable[IMutator]:
        return self._source_mutators

    def get_target_mutators(self) -> Iterable[IMutator]:
        return self._target_mutators

    def load(self) -> None:
        raise ErrOperationNotSupported(
            "while accessing an internal template instance.",
            "The way in which it was accessed is not supported."
        )

    def detect_async(self, /, *, target: IImage) -> Future:
        raise ErrOperationNotSupported(
            "while accessing an internal template instance.",
            "The way in which it was accessed is not supported."
        )

    def detect(self, /, **kwargs) -> ISupervisionResult:
        raise ErrOperationNotSupported(
            "while accessing an internal template instance.",
            "The way in which it was accessed is not supported."
        )

    def get_source_image_path(self) -> str:
        if os.path.isabs(self._source):
            return self._source
        path_to_template_dir = os.path.dirname(self._path_to_template)
        path = os.path.join(path_to_template_dir, self._source)
        return os.path.normpath(path)

    def get_image(self) -> IImage:
        return InternalImage(path=self.get_source_image_path())

    def get_mutated_image(self) -> IImage:
        img = self.get_image()
        img.apply_mutators(*self._source_mutators)
        return img

    @property
    def identifier(self) -> str:
        return self._template_id

    @property
    def name(self) -> str:
        return self._name

    @property
    def width(self) -> int:
        return self._width

    @property
    def height(self) -> int:
        return self._height

    @property
    def keypoints(self) -> Iterable[InternalKeypoint]:
        for keypoint_id in self._keypoints:
            yield self._keypoints[keypoint_id]

    @property
    def features(self) -> Iterable[InternalFeature]:
        for feature_id in self._features:
            yield self._features[feature_id]

    def validate(self):
        for feature in self.features:
            feature.validate_feature_class()

    def get_matcher(self, /) -> IMatcher:
        matcher_id = self._matching["engine"]

        matcher_configs: dict = self._matching["config"]
        matcher_config: ConfigDict = matcher_configs.get(matcher_id, {})

        return get_internal_context().get_matcher(matcher_id, matcher_config)

    def get_supervisor(self, /) -> ISupervisor:
        supervisor_id = self._supervision["engine"]
        supervisor_config_generic = self._supervision["config"]

        if supervisor_id in supervisor_config_generic:
            supervisor_config: ConfigDict = supervisor_config_generic[supervisor_id]
        else:
            get_internal_afi().warn(Verbosity.INFO, f"Could not find any configuration entries for the '{supervisor_id}' supervisor.")
            supervisor_config: ConfigDict = {}

        return get_internal_context().get_supervisor(supervisor_id, supervisor_config)

    def get_supervision_config(self) -> dict:
        return self._supervision["config"]

    def get_feature_classes(self) -> FeatureClassManager:
        return self._feature_class_manager

    def get_feature(self, feature_id: str, /) -> InternalFeature | None:

        if feature_id not in self._features:
            return None

        return self._features[feature_id]

    def get_keypoint(self, keypoint_id: str, /) -> InternalKeypoint | None:

        if keypoint_id not in self._keypoints:
            return None

        return self._keypoints[keypoint_id]

    def get_path(self) -> str:
        return self._path_to_template

    def _run_supervisor(self, keypoint_matching_result: InternalMatchingResult, /) -> InternalSupervisionResult | None:

        supervisor = self.get_supervisor()
        supervisor.setup(self, keypoint_matching_result)

        supervision_result_choice_engine = self._supervision["result"]
        results: List[InternalSupervisionResult] = [
            InternalSupervisionResult(supervision_result, self, keypoint_matching_result)
            for supervision_result in supervisor.supervise(self, keypoint_matching_result)
        ]

        if len(results) == 0:
            return None

        for result in results:
            get_internal_afi().info(
                Verbosity.INFO_VERBOSE,
                f"Got result with score {result.score} and error {result.get_weighted_mse()} from supervisor '{supervisor}'."
            )

        if supervision_result_choice_engine == _SUPERVISION_RESULT_FIRST:
            return results[0]

        if supervision_result_choice_engine == _SUPERVISION_RESULT_RANDOM:
            return random.choice(results)

        if supervision_result_choice_engine == _SUPERVISION_RESULT_BEST_MSE:

            best_result = results[0]
            best_result_mse = best_result.get_weighted_mse()

            for result_id, result in enumerate(results):
                result_mse = result.get_weighted_mse()

                get_internal_afi().info(Verbosity.INFO_VERBOSE, f"Result #{result_id + 1} has MSE {result_mse}.")

                if result_mse < best_result_mse:
                    best_result_mse = result_mse
                    best_result = result

            get_internal_afi().info(Verbosity.INFO_VERBOSE, f"Best result has MSE {best_result_mse}.")

            return best_result

        if supervision_result_choice_engine == _SUPERVISION_RESULT_BEST_SCORE:

            best_result = results[0]
            best_result_mse = best_result.get_weighted_mse()
            best_result_score = best_result.score

            for result_id, result in enumerate(results):
                result_score = result.score
                result_mse = result.get_weighted_mse()

                get_internal_afi().info(Verbosity.INFO_VERBOSE, f"Result #{result_id + 1} has score {result_score}.")

                if result_score > best_result_score or result_score == best_result_score and result_mse < best_result_mse:
                    best_result_mse = result_mse
                    best_result_score = result_score
                    best_result = result

            get_internal_afi().info(Verbosity.INFO_VERBOSE, f"Best result has score {best_result_score} and MSE {best_result_mse}.")

            return best_result

        raise ErrInvalidIdentifier(
            "while running supervisor.",
            f"Invalid supervision result choice engine '{supervision_result_choice_engine}'."
        )

    def do_detect(self, target: np.ndarray, /) -> InternalSupervisionResult:
        # find all patterns in the target image

        # prepare target image
        get_internal_afi().update_status("Preparing target image...")

        # apply mutators to the target image
        for mutator in self._target_mutators:
            target = mutator.mutate(target)

        get_internal_afi().update_status("Running matching phase...")

        _timer = Timer()

        with _timer:
            # start matching
            matcher: IMatcher = self.get_matcher()
            matcher.setup(target, self)

            for keypoint in self.keypoints:
                get_internal_afi().info(Verbosity.DEBUG, f"Running matcher '{matcher}' for keypoint '{keypoint.identifier}'.")
                assert isinstance(keypoint, InternalKeypoint)
                matcher.match(keypoint)

            keypoint_matching_result = InternalMatchingResult(self)

            for keypoint in self.keypoints:
                for match in matcher.get_matches_for_keypoint(keypoint):
                    assert isinstance(match, IMatch)
                    keypoint_matching_result.add_match(match)

            keypoint_matching_result.validate()
            assert keypoint_matching_result.get_total_match_count() > 0

        get_internal_afi().info(
            Verbosity.INFO,
            f"Matching succeeded in {_timer.get_real_time():.2f} seconds of real time "
            f"and {_timer.get_cpu_time():.2f} seconds of CPU time."
        )

        get_internal_afi().update_status("Running supervision phase...")

        with _timer:
            # run supervision to obtain correspondence between template and target regions
            supervision_result = self._run_supervisor(keypoint_matching_result)

        get_internal_afi().info(
            Verbosity.INFO,
            f"Supervision succeeded in {_timer.get_real_time():.2f} seconds of real time "
            f"and {_timer.get_cpu_time():.2f} seconds of CPU time."
        )

        if supervision_result is None:
            raise ErrSupervisionCorrespondenceNotFound(
                "while processing a supervision result.",
                f"Could not establish correspondence of the image with the '{self.identifier}' template."
            )

        get_internal_afi().info(
            Verbosity.DEBUG_VERBOSE,
            f"Supervision result: Delta = {supervision_result.delta} Delta' = {supervision_result.delta_prime} "
            f"M = {supervision_result.transformation_matrix}"
        )

        # TODO: visualizations
        """
        if get_internal_context().visualization_generation_enabled():
            supervision_result_visualizer = SupervisionResultVisualizer(supervision_result, target)
            visualization = supervision_result_visualizer.render()
            get_internal_context().export_image(visualization, file_name="matches.png")
        """

        return supervision_result

    def __str__(self):
        return f"{self.name} ({self._source}, {len(self._keypoints)} keypoints, {len(self._features)} features)"
