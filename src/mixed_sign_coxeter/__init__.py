"""mixed_sign_coxeter: Python library for reflection systems and mixed-sign Coxeter systems."""

from .catalog import (
    AnTableEntry,
    A_n_sign_table,
    classify_signature,
    fast_integer_group_order,
    finite_even_odd_cycle_determinants,
    mahler_measure,
    table_a1,
    table_a2,
)
from .group import (
    element_order,
    enumerate_group,
    evaluate_word,
    find_two_deletions,
    generate_roots,
    is_positive_vector,
)
from .mixed_sign import MixedSignCoxeterGraph
from .reflection_system import ReflectionSystem, Signature

__all__ = [
    "AnTableEntry",
    "A_n_sign_table",
    "MixedSignCoxeterGraph",
    "ReflectionSystem",
    "Signature",
    "classify_signature",
    "element_order",
    "enumerate_group",
    "evaluate_word",
    "fast_integer_group_order",
    "find_two_deletions",
    "finite_even_odd_cycle_determinants",
    "generate_roots",
    "is_positive_vector",
    "mahler_measure",
    "table_a1",
    "table_a2",
]

