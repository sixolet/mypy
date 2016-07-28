from typing import (
    List,
    Optional,
    Tuple,
    Dict,
)
from collections import defaultdict

from mypy.types import (
    ANY_TYPE_STRATEGY,
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

def infer_expansions_for_callable(
        callee: CallableType,
        arg_types: List[Optional[Type]],
        arg_kinds: List[int],
        formal_to_actual: List[List[int]],
) -> List[Tuple[TypeVarId, int]]: # Tuples of type variable id -> number of
                                  # expansiont type vars
    """Figure out how the variadic type variables should expand
    """
    expansions = [] # type: List[Tuple[TypeVarId, int]]
    for i, actuals in enumerate(formal_to_actual):
        callee_kind = callee.arg_kinds[i]
        callee_arg = callee.arg_types[i]
        if callee_kind == nodes.ARG_STAR and callee_arg.accept(IsVariadic()):
            expansions.append(
                (callee_arg.accept(FetchVariadicTypeVar()), len(actuals))
            )
        elif callee_kind == nodes.ARG_NAMED and callee_arg.accept(IsVariadic()):
            # How do we deal with **args?
            pass
        else:
            for actual in actuals:
                if arg_types[actual] is None:
                    continue
                expansions.extend(infer_expansions(
                    callee.arg_types[i],
                    arg_types[actual],
                    arg_kinds[actual],
                ))
    return expansions

def expand_variadic_callable(
        callee: CallableType,
        arg_types: List[Optional[Type]],
        arg_kinds: List[int],
        formal_to_actual: List[List[int]],
) -> CallableType:
    expansions = infer_expansions_for_callable(
        callee,
        arg_types,
        arg_kinds,
        formal_to_actual)
    exps = {} # type: Dict[TypeVarId, int]
    for var_id, num in expansions:
        if var_id in exps:
            if exps[var_id] != num:
                raise TypeError("TODO: found different expansion numbers")
        exps[var_id] = num
    substitutions = defaultdict(list) # type: Dict[TypeVarId, List[TypeVarId]]
    additional_variables = []
    new_types = [] # type: List[Type]
    new_kinds = [] # type: List[int]
    new_names = [] # type: List[str]
    for typ, kind, name in zip(callee.arg_types, callee.arg_kinds, callee.arg_names):
        if kind == nodes.ARG_STAR and typ.accept(IsVariadic()):
            # Substitute in for the expansion
            old_id = typ.accept(FetchVariadicTypeVar())
            assert old_id in exps
            for idx in range(exps[old_id]):
                new_id = TypeVarId.new(1) # Uhh is this a "meta" variable?
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
            # TODO: Recursively descend here to expland any tuple or types of
            # callable args.
            new_types.append(typ)
            new_kinds.append(kind)
            new_names.append(name)
    new_variables = [
        var for var in callee.variables if var.id not in substitutions
    ] + additional_variables

    # TODO: Expand type vars in return type
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



def infer_expansions(
        callee_arg_type: Type,
        arg_type: Type,
        arg_kind: int
) -> List[Tuple[TypeVarId, int]]:
    if arg_kind == nodes.ARG_STAR:
        if isinstance(arg_type, Instance):
            if arg_type.args and callee_arg_type.is_variadic():
                return []
    return []


class IsVariadic(TypeQuery):
    def __init__(self):
        return super(IsVariadic, self).__init__(False, ANY_TYPE_STRATEGY)

    def visit_type_var(self, t: TypeVarType) -> bool:
        return t.variadic

class FetchVariadicTypeVar(TypeFold[TypeVarId]):

    def __init__(self):
        return super(FetchVariadicTypeVar, self).__init__(None, None)


    def combine(self, res: TypeVarId, n: TypeVarId):
        if res is not None:
            return res
        return n

    def visit_type_var(self, t: TypeVarType) -> TypeVarId:
        if t.variadic:
            return t.id
#class VariadicExpanderVisitor(TypeVisitor[List[Tuple[TypeVarId, int]]]):

class SubstituteVariable(TypeTranslator):

    def __init__(self, old: TypeVarId, new: TypeVarId, idx: int):
        self.old = old
        self.new = new
        self.idx = idx
        self.var = None # type: TypeVarDef

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

    substitutions = None # type: Dict[TypeVarId, List[TypeVarId]]

    def __init__(self, substitutions: Dict[TypeVarId, List[TypeVarId]]):
        self.substitutions = substitutions

    def visit_tuple_type(self, t: TupleType) -> Type:
        if t.expand_last_item:

            variadic_id = t.accept(FetchVariadicTypeVar())
            if variadic_id in self.substitutions:
                # We have some type variables to substitute in
                new_items = t.items[:-1] # all but the last
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
