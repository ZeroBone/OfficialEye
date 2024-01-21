from typing import Dict

from officialeye._internal.diffobject.difference_expansion import DiffObjectExpansion
from officialeye._internal.template.feature_class.const import IMPLICIT_FEATURE_CLASS_BASE_INSTANCE_ID
from officialeye._internal.template.schema.schema import feature_class_object_specification


class FeatureClass:

    def __init__(self, manager, class_id: str, def_dict: Dict[str, any], /):
        self._manager = manager
        self.class_id = class_id
        self.is_inline = False

        self._data = {
            "abstract": False,
            "inherits": IMPLICIT_FEATURE_CLASS_BASE_INSTANCE_ID,
            **def_dict
        }

    def is_global_base_class(self) -> bool:
        return self.class_id == IMPLICIT_FEATURE_CLASS_BASE_INSTANCE_ID

    def get_parent_class(self):
        assert self.class_id != IMPLICIT_FEATURE_CLASS_BASE_INSTANCE_ID, "The global base class has no parent"
        parent_id = self._data["inherits"]
        return self._manager.get_class(parent_id)

    def is_abstract(self) -> bool:
        return self._data["abstract"]

    def get_features(self):
        """
        Generates all features that inherit this class (or belong to it directly)
        """

        template = self._manager.get_template()

        for cur_feature in template.features():
            cur_feature_class = cur_feature.get_feature_class()

            if cur_feature_class is None:
                continue

            # search in cur_feature's parents for the present class
            while not cur_feature_class.is_global_base_class():

                if cur_feature_class == self:
                    yield cur_feature
                    # we already found this class among the parents, no need to go deeper
                    break

                cur_feature_class = cur_feature_class.get_parent_class()

    def inline(self):
        """
        Computes all inherited attributes and applies diffs accordingly.
        The result gets cached so that they do not have to be computed every time.

        Raises: DiffObjectException
        """

        if self.is_inline:
            return

        class_parents_stack = []
        current_class = self

        while not current_class.is_global_base_class():
            class_parents_stack.append(current_class)
            current_class = current_class.get_parent_class()

        if len(class_parents_stack) == 0:
            class_parents_stack = [self]

        expansion = DiffObjectExpansion(feature_class_object_specification)

        while len(class_parents_stack) > 0:
            ancestor = class_parents_stack.pop()
            expansion.add(ancestor._data)

            if ancestor.is_abstract():
                ancestor_inlined = expansion.get_current_partial_object()
            else:
                ancestor_inlined = expansion.get_full_object()

            ancestor.is_inline = True
            ancestor._data = ancestor_inlined

        assert self.is_inline

    def get_data(self) -> Dict[str, any]:
        return self._data
