"""Defines experimental extensions to the standard "typing" module that are
supported by the mypy typechecker.

Example usage:
    from mypy_extensions import TypedDict
"""

from typing import Any

# NOTE: This module must support Python 2.7 in addition to Python 3.x


def TypedDict(typename, fields):
    """TypedDict creates a dictionary type that expects all of its
    instances to have a certain set of keys, with each key
    associated with a value of a consistent type. This expectation
    is not checked at runtime but is only enforced by typecheckers.
    """
    def new_dict(*args, **kwargs):
        return dict(*args, **kwargs)

    new_dict.__name__ = typename
    new_dict.__supertype__ = dict
    return new_dict

class Arg(object):
    def __init__(name=None, typ=Any, keyword_only=False):
        self.name = name
        self.typ = typ
        self.named_only = named_only

class DefaultArg(object):
    def __init__(name=None, typ=Any, keyword_only=False):
        self.name = name
        self.typ = typ
        self.named_only = named_only

class StarArg(object):
    def __init__(typ=Any) -> None:
        self.typ = typ

class KwArg(object):
    def __init__(typ=Any) -> None:
        self.typ = typ
