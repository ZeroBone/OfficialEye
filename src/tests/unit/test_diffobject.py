import strictyaml as yml


def test_01():
    from officialeye._internal.diffobject.difference_expansion import DiffObjectExpansion
    from officialeye._internal.diffobject.specification import DiffObjectSpecification
    from officialeye._internal.diffobject.specification_entries.string import StringSpecificationEntry

    spec = DiffObjectSpecification({
        "one": StringSpecificationEntry(yml.Any()),
        "two": StringSpecificationEntry(yml.Any()),
        "three": StringSpecificationEntry(yml.Any()),
    })

    expansion = DiffObjectExpansion(spec)

    expansion.add({
        "one": "1"
    })

    assert expansion.get_current_partial_object() == {
        "one": "1"
    }

    expansion.add({
        "two": "2"
    })

    assert expansion.get_current_partial_object() == {
        "one": "1",
        "two": "2"
    }

    expansion.add({
        "three": "3"
    })

    assert expansion.get_full_object() == {
        "one": "1",
        "two": "2",
        "three": "3"
    }


def test_02():
    from officialeye._internal.diffobject.difference_expansion import DiffObjectExpansion
    from officialeye._internal.diffobject.difference_modes import DIFF_MODE_ADD, DIFF_MODE_OVERRIDE
    from officialeye._internal.diffobject.specification import DiffObjectSpecification
    from officialeye._internal.diffobject.specification_entries.string import StringSpecificationEntry

    spec = DiffObjectSpecification({
        "one": StringSpecificationEntry(yml.Any()),
        "two": StringSpecificationEntry(yml.Any()),
        "three": StringSpecificationEntry(yml.Any()),
    })

    expansion = DiffObjectExpansion(spec)

    expansion.add({
        "one": "1"
    })

    expansion.add({
        "two": "2"
    })

    assert expansion.get_current_partial_object() == {
        "one": "1",
        "two": "2"
    }

    expansion.add({
        "three": "3"
    })

    expansion.add({
        "two": "lol",
        "$two": DIFF_MODE_ADD,
        "three": "4",
        "$three": DIFF_MODE_OVERRIDE
    })

    assert expansion.get_full_object() == {
        "one": "1",
        "two": "2lol",
        "three": "4"
    }


def test_03():
    from officialeye._internal.diffobject.difference_expansion import DiffObjectExpansion
    from officialeye._internal.diffobject.difference_modes import DIFF_MODE_ADD
    from officialeye._internal.diffobject.specification import DiffObjectSpecification
    from officialeye._internal.diffobject.specification_entries.integer import IntegerSpecificationEntry
    from officialeye._internal.diffobject.specification_entries.list import ListSpecificationEntry
    from officialeye._internal.diffobject.specification_entries.string import StringSpecificationEntry

    spec = DiffObjectSpecification({
        "one": StringSpecificationEntry(yml.Any()),
        "two": {
            "a": ListSpecificationEntry(yml.Any()),
            "b": IntegerSpecificationEntry(yml.Int())
        }
    })

    expansion = DiffObjectExpansion(spec)

    expansion.add({
        "one": "1",
        "two": {
            "a": [1, 2, 3, 4]
        }
    })

    assert expansion.get_current_partial_object() == {
        "one": "1",
        "two": {
            "a": [1, 2, 3, 4]
        }
    }

    expansion.add({
        "two": {
            "a": [5, 6],
            "$a": DIFF_MODE_ADD,
            "b": 0xff
        }
    })

    assert expansion.get_full_object() == {
        "one": "1",
        "two": {
            "a": [1, 2, 3, 4, 5, 6],
            "b": 0xff
        }
    }
