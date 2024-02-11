"""
Root module.
"""

# Context
# noinspection PyProtectedMember
from officialeye._api.context import Context

# Config
# noinspection PyProtectedMember
from officialeye._api.config import Config, MutatorConfig, MatcherConfig, SupervisorConfig

# Image-processing
# noinspection PyProtectedMember
from officialeye._api.image import IImage, Image

# Mutators
# noinspection PyProtectedMember
from officialeye._api.mutator import Mutator, IMutator

# Template-related
# noinspection PyProtectedMember
from officialeye._api.template.template import ITemplate, Template

# Regions, features and keypoints
# noinspection PyProtectedMember
from officialeye._api.template.region import IRegion, Region
# noinspection PyProtectedMember
from officialeye._api.template.feature import IFeature, Feature
# noinspection PyProtectedMember
from officialeye._api.template.keypoint import IKeypoint, Keypoint

# Matching-related imports
# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch, Match
# noinspection PyProtectedMember
from officialeye._api.template.matcher import IMatcher, Matcher
# noinspection PyProtectedMember
from officialeye._api.template.matching_result import IMatchingResult

# Supervision-related imports
# noinspection PyProtectedMember
from officialeye._api.template.supervisor import ISupervisor, Supervisor
# noinspection PyProtectedMember
from officialeye._api.template.supervision_result import ISupervisionResult, SupervisionResult

# Misc
# noinspection PyProtectedMember
from officialeye._api.future import Future, wait
