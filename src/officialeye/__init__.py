"""
Root module.
"""

# disable unused imports ruff check
# ruff: noqa: F401

# Config
# noinspection PyProtectedMember
from officialeye._api.config import Config, InterpretationConfig, MatcherConfig, MutatorConfig, SupervisorConfig

# Context
# noinspection PyProtectedMember
from officialeye._api.context import Context

# Misc
# noinspection PyProtectedMember
from officialeye._api.future import Future, wait

# Image-processing
# noinspection PyProtectedMember
from officialeye._api.image import IImage, Image

# Mutators
# noinspection PyProtectedMember
from officialeye._api.mutator import IMutator, Mutator

# noinspection PyProtectedMember
from officialeye._api.template.feature import IFeature

# Interpretation-related imports
# noinspection PyProtectedMember
from officialeye._api.template.interpretation import IInterpretation, Interpretation

# noinspection PyProtectedMember
from officialeye._api.template.interpretation_result import IInterpretationResult

# noinspection PyProtectedMember
from officialeye._api.template.keypoint import IKeypoint

# Matching-related imports
# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch, Match

# noinspection PyProtectedMember
from officialeye._api.template.matcher import IMatcher, Matcher

# noinspection PyProtectedMember
from officialeye._api.template.matching_result import IMatchingResult

# Regions, features and keypoints
# noinspection PyProtectedMember
from officialeye._api.template.region import IRegion, Region

# noinspection PyProtectedMember
from officialeye._api.template.supervision_result import ISupervisionResult, SupervisionResult

# Supervision-related imports
# noinspection PyProtectedMember
from officialeye._api.template.supervisor import ISupervisor, Supervisor

# Template-related
# noinspection PyProtectedMember
from officialeye._api.template.template import ITemplate, Template
