from typing import (
    List,
    Optional,
    Tuple,
    Dict,
)
from collections import defaultdict

from mypy.types import (
    ANY_TYPE_STRATEGY,
    AnyType,
    CallableType,
    TupleType,
    Type,
    TypeQuery,
    TypeFold,
    TypeTranslator,
    TypeVarDef,
    TypeVarType,
    TypeVarId,
)

from mypy import nodes
from mypy.nodes import Node
from mypy.erasetype import TypeVarEraser


def infer_expansions_for_callable(
        callee: CallableType,
        args: List[Optional[Node]],
        arg_kinds: List[int],
        formal_to_actual: List[List[int]],
) -> List[Tuple[TypeVarId, int]]:
    """Figure out how the variadic type variables should expand
    """
    expansions = []  # type: List[Tuple[TypeVarId, int]]
    for i, actuals in enumerate(formal_to_actual):
        callee_kind = callee.arg_kinds[i]
        callee_arg = callee.arg_types[i]
        if callee_kind == nodes.ARG_STAR and callee_arg.accept(IsVariadic()):
            if any(k != nodes.ARG_POS for k in (arg_kinds[actual] for actual in actuals)):
                # Somebody splatted in an arg here, so don't make any assumptions.
                pass
            else:
                expansions.append(
                    (callee_arg.accept(FetchVariadicTypeVar()), len(actuals)))
        elif callee_kind == nodes.ARG_NAMED and callee_arg.accept(IsVariadic()):
            # How do we deal with **args?
            pass
        else:
            for actual in actuals:
                if args[actual] is None:
                    continue
                pass  # Do a thing with tuples of Ts and callables in argument lists.
    return expansions


def expand_variadic_callable(
        callee: CallableType,
        args: List[Optional[Node]],
        arg_kinds: List[int],
        formal_to_actual: List[List[int]],
) -> CallableType:
    expansions = infer_expansions_for_callable(
        callee,
        args,
        arg_kinds,
        formal_to_actual)
    exps = {}  # type: Dict[TypeVarId, int]
    for var_id, num in expansions:
        if var_id in exps:
            if exps[var_id] != num:
                raise TypeError("TODO: found different expansion numbers")
        exps[var_id] = num
    substitutions = defaultdict(list)  # type: Dict[TypeVarId, List[TypeVarId]]
    additional_variables = []
    new_types = []  # type: List[Type]
    new_kinds = []  # type: List[int]
    new_names = []  # type: List[str]
    for typ, kind, name in zip(callee.arg_types, callee.arg_kinds, callee.arg_names):
        if kind == nodes.ARG_STAR and typ.accept(IsVariadic()):
            # Substitute in for the expansion
            old_id = typ.accept(FetchVariadicTypeVar())  # type: TypeVarId
            if old_id in exps:
                for idx in range(exps[old_id]):
                    new_id = TypeVarId.new(1)  # Uhh is this a "meta" variable?
                    substitutions[old_id].append(new_id)
                    new_kinds.append(nodes.ARG_POS)
                    substitutor = SubstituteVariable(old_id, new_id, idx)
                    new_types.append(typ.accept(substitutor))
                    additional_variables.append(substitutor.var)
                    if name is not None:
                        new_names.append("%s_%d" % (name, idx))
                    else:
                        new_names.append(None)
            else:
                new_kinds.append(nodes.ARG_STAR)
                new_types.append(typ.accept(TypeVarEraser(
                            lambda i: old_id == i, AnyType())))
                new_names.append(name)
        else:
            # TODO: Recursively descend here to expland any tuple or types of
            # callable args.
            new_types.append(typ)
            new_kinds.append(kind)
            new_names.append(name)
    new_variables = [
        var for var in callee.variables if var.id not in substitutions
    ] + additional_variables

    # Apply the substitutions we've calculated to all the new args
    new_types = [typ.accept(ExpandVariadic(substitutions)) for typ in new_types]

    # Apply the substitutions we've calculated to the return type
    new_ret_type = callee.ret_type.accept(ExpandVariadic(substitutions))

    return CallableType(
        arg_types=new_types,
        arg_kinds=new_kinds,
        arg_names=new_names,
        ret_type=new_ret_type,
        fallback = callee.fallback,
        name = callee.name,
        definition = callee.definition,
        variables = new_variables,
        line = callee.line,
        is_ellipsis_args = callee.is_ellipsis_args,
        implicit = callee.implicit,
        is_classmethod_class = callee.is_classmethod_class,
        special_sig = callee.special_sig,
    )


class IsVariadic(TypeQuery):
    def __init__(self) -> None:
        super(IsVariadic, self).__init__(False, ANY_TYPE_STRATEGY)

    def visit_type_var(self, t: TypeVarType) -> bool:
        return t.variadic

    def visit_tuple_type(self, t: TupleType) -> bool:
        if t.expand_last_item:
            # A tuple type is itself not variadic if it contains an expansion
            return False
        else:
            return super(IsVariadic, self).visit_tuple_type(t)

    def visit_callable_type(self, t: CallableType) -> bool:
        # A callable type is itself not variadic if it contains an expansion
        if len(t.arg_kinds) > 0 and t.arg_kinds[-1] == nodes.ARG_STAR:
            return False
        else:
            return super(IsVariadic, self).visit_callable_type(t)


class FetchVariadicTypeVar(TypeFold[TypeVarId]):

    def __init__(self) -> None:
        super(FetchVariadicTypeVar, self).__init__(None, None)

    def combine(self, res: TypeVarId, n: TypeVarId):
        if res is not None:
            return res
        return n

    def visit_type_var(self, t: TypeVarType) -> TypeVarId:
        if t.variadic:
            return t.id

    def visit_tuple_type(self, t: TupleType) -> TypeVarId:
        if t.expand_last_item:
            return self.fold_types(t.items[:-1])
        else:
            return super(IsVariadic, self).visit_tuple_type(t)

    def visit_callable_type(self, t: CallableType) -> TypeVarId:
        # A callable type is itself not variadic if it contains an expansion
        if len(t.arg_kinds) > 0 and t.arg_kinds[-1] == nodes.ARG_STAR:
            return self.fold_types(t.arg_types[:-1])
        else:
            return super(IsVariadic, self).visit_callable_type(t)


class SubstituteVariable(TypeTranslator):

    def __init__(self, old: TypeVarId, new: TypeVarId, idx: int) -> None:
        self.old = old
        self.new = new
        self.idx = idx
        self.var = None  # type: TypeVarDef

    def visit_type_var(self, t: TypeVarType) -> Type:
        if t.id == self.old:
            self.var = TypeVarDef(
                name="%s_%d" % (t.name, self.idx),
                id=self.new,
                values=t.values,
                upper_bound=t.upper_bound,
                variance=t.variance,
                variadic=False,
            )
            return TypeVarType(self.var, t.line)
        else:
            return t


class ExpandVariadic(TypeTranslator):

    substitutions = None  # type: Dict[TypeVarId, List[TypeVarId]]

    def __init__(self, substitutions: Dict[TypeVarId, List[TypeVarId]]) -> None:
        self.substitutions = substitutions

    def visit_tuple_type(self, t: TupleType) -> Type:
        if t.expand_last_item:

            variadic_id = t.items[-1].accept(FetchVariadicTypeVar())
            if variadic_id in self.substitutions:
                # We have some type variables to substitute in
                new_items = t.items[:-1]  # all but the last, which is the variadic
                for idx, new_var_id in enumerate(self.substitutions[variadic_id]):
                    substitutor = SubstituteVariable(variadic_id, new_var_id, idx)
                    new_items.append(t.items[-1].accept(substitutor))
                return TupleType(
                    self.translate_types(new_items),
                    t.fallback,
                    implicit=t.implicit,
                    expand_last_item=False
                )
            else:
                # Use the fallback, because we have no way of substituting.
                return t.fallback
        else:
            return super(ExpandVariadic, self).visit_tuple_type(t)

    def visit_callable_type(self, t: CallableType) -> TypeVarId:
        # A callable type is itself not variadic if it contains an expansion
        if len(t.arg_kinds) > 0 and t.arg_kinds[-1] == nodes.ARG_STAR and t.arg_types[-1].accept(IsVariadic()):
            variadic_id = t.arg_types[-1].accept(FetchVariadicTypeVar())
            if variadic_id in self.substitutions:
                new_args = t.arg_types[:-1]  # all but the last, which is the variadic
                new_kinds = t.arg_kinds[:-1]
                new_names = t.arg_names[:-1]
                for idx, new_var_id in enumerate(self.substitutions[variadic_id]):
                    substitutor = SubstituteVariable(variadic_id, new_var_id, idx)
                    new_args.append(t.arg_types[-1].accept(substitutor))
                    new_kinds.append(nodes.ARG_POS)
                    new_names.append(None)
                return t.copy_modified(
                    arg_types=self.translate_types(new_args),
                    arg_kinds=new_kinds,
                    arg_names=new_names,
                    ret_type=t.ret_type.accept(self),
                )
            else:
                new_args = t.arg_types[:-1]
                new_args.append(
                    t.arg_types[-1].accept(TypeVarEraser(
                            lambda i: i == variadic_id,
                            AnyType(implicit=True))))
                return t.copy_modified(arg_types=new_args)
        else:
            return super(ExpandVariadic, self).visit_callable_type(t)
