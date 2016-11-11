"""Type parser"""

from typing import List, Tuple, Union, Optional

from mypy.types import (
    Type, UnboundType, TupleType, ArgumentList, CallableType, StarType,
    EllipsisType, AnyType
)
from mypy.lex import Token, Name, StrLit, lex
from mypy import nodes


none = Token('')  # Empty token


class TypeParseError(Exception):
    def __init__(self, token: Token, index: int, message: Optional[str] = None) -> None:
        super().__init__()
        self.token = token
        self.index = index
        self.message = message


def parse_type(tok: List[Token], index: int) -> Tuple[Type, int]:
    """Parse a type.

    Return (type, index after type).
    """

    p = TypeParser(tok, index)
    return p.parse_type(), p.index()


def parse_types(tok: List[Token], index: int) -> Tuple[Type, int]:
    """Parse one or more types separated by commas (optional parentheses).

    Return (type, index after type).
    """

    p = TypeParser(tok, index)
    return p.parse_types(), p.index()


class TypeParser:
    def __init__(self, tok: List[Token], ind: int) -> None:
        self.tok = tok
        self.ind = ind

    def index(self) -> int:
        return self.ind

    def parse_type(self) -> Type:
        """Parse a type."""
        t = self.current_token()
        if t.string == '(':
            return self.parse_parens()
        if isinstance(t, Name):
            return self.parse_named_type()
        elif t.string == '[':
            return self.parse_argument_list()
        elif t.string == '*':
            return self.parse_star_type()
        elif t.string == '...':
            return self.parse_ellipsis_type()
        elif isinstance(t, StrLit):
            # Type escaped as string literal.
            typestr = t.parsed()
            line = t.line
            self.skip()
            try:
                result = parse_str_as_type(typestr, line)
            except TypeParseError as e:
                raise TypeParseError(e.token, self.ind)
            return result
        else:
            self.parse_error()

    def parse_parens(self) -> Type:
        self.expect('(')
        types = self.parse_types()
        self.expect(')')
        return types

    def parse_types(self) -> Type:
        """ Parse either a single type or a comma separated
        list of types as a tuple type. In the latter case, a
        trailing comma is needed when the list contains only
        a single type (and optional otherwise).

        int   ->   int
        int,  ->   TupleType[int]
        int, int, int  ->  TupleType[int, int, int]
        """
        type = self.parse_type()
        if self.current_token_str() == ',':
            items = [type]
            while self.current_token_str() == ',':
                self.skip()
                if self.current_token_str() == ')':
                    break
                items.append(self.parse_type())
            type = TupleType(items, None, type.line, implicit=True)
        return type

    def parse_argument_spec(self) -> Tuple[Type, Optional[str], int]:
        current = self.current_token()
        nxt = self.next_token()
        # This is a small recreation of a subset of parsing a CallExpr; just
        # enough to parse what happens in an arugment list.
        # TODO: Doesn't handle an explicit name of None yet.
        if isinstance(current, Name) and nxt is not None and nxt.string == '(':
            arg_const = self.expect_type(Name).string
            name = None # type: Optional[str]
            typ = AnyType # type: Type
            if arg_const == 'Arg':
                kind = nodes.ARG_POS
                name, typ, keyword_only = self.parse_arguments(
                    read_name = True,
                    read_typ = True,
                    read_keyword_only = True)
                if keyword_only:
                    kind = nodes.ARG_NAMED
            elif arg_const == 'DefaultArg':
                kind = nodes.ARG_OPT
                name, typ, keyword_only = self.parse_arguments(
                    read_name = True,
                    read_typ = True,
                    read_keyword_only = True)
                if keyword_only:
                    kind = nodes.ARG_NAMED_OPT
            elif arg_const == 'StarArg':
                # Takes one type
                kind = nodes.ARG_STAR
                _, typ, _ = self.parse_arguments(
                    read_name = False,
                    read_typ = True,
                    read_keyword_only = False)
            elif arg_const == 'KwArg':
                # Takes one type
                kind = nodes.ARG_STAR2
                _, typ, _ = self.parse_arguments(
                    read_name = False,
                    read_typ = True,
                    read_keyword_only = False)
            else:
                self.parse_error()
            return typ, name, kind
        else:
            return self.parse_type(), None, nodes.ARG_POS

    def parse_arguments(self,
                        *,
                        read_name: bool,
                        read_typ: bool,
                        read_keyword_only: bool) -> Tuple[
                            Optional[str],
                            Optional[Type],
                            bool]:
        self.expect('(')
        name = None
        typ = AnyType
        keyword_only = False
        try:
            if self.current_token_str() == ')':
                return name, typ, keyword_only
            if read_name:
                if self.current_token_str() != 'None':
                    name = self.expect_type(StrLit).parsed()
                else:
                    self.skip()
                if self.current_token_str() == ')':
                    return name, typ, keyword_only
                else:
                    self.expect(',')
            if read_typ:
                typ = self.parse_type()
                if self.current_token_str() == ')':
                    return name, typ, keyword_only
                else:
                    self.expect(',')
            if read_keyword_only:
                if self.current_token_str() == 'True':
                    keyword_only = True
                    self.skip()
                else:
                    self.expect('False')
                if self.current_token_str() == ')':
                    return name, typ, keyword_only
                else:
                    self.expect(',')
        finally:
            self.expect(')')


    def parse_argument_list(self) -> ArgumentList:
        """Parse type list [t, ...]."""
        lbracket = self.expect('[')
        commas = []  # type: List[Token]
        items = []  # type: List[Type]
        names = [] # type: List[Optional[str]]
        kinds = [] # type: List[int]
        while self.current_token_str() != ']':
            t, name, kind = self.parse_argument_spec()
            items.append(t)
            names.append(name)
            kinds.append(kind)

            if self.current_token_str() != ',':
                break
            commas.append(self.skip())
        self.expect(']')
        return ArgumentList(items, names, kinds, line=lbracket.line)

    def parse_named_type(self) -> Type:
        line = self.current_token().line
        name = ''
        components = []  # type: List[Token]

        components.append(self.expect_type(Name))
        name += components[-1].string

        while self.current_token_str() == '.':
            components.append(self.skip())
            t = self.expect_type(Name)
            components.append(t)
            name += '.' + t.string

        commas = []  # type: List[Token]
        args = []  # type: List[Type]
        if self.current_token_str() == '[':
            self.skip()
            while True:
                typ = self.parse_type()
                args.append(typ)
                if self.current_token_str() != ',':
                    break
                commas.append(self.skip())

            self.expect(']')

        typ = UnboundType(name, args, line)
        return typ

    def parse_star_type(self) -> Type:
        star = self.expect('*')
        type = self.parse_type()
        return StarType(type, star.line)

    def parse_ellipsis_type(self) -> Type:
        ellipsis = self.expect('...')
        return EllipsisType(ellipsis.line)

    # Helpers

    def skip(self) -> Token:
        self.ind += 1
        return self.tok[self.ind - 1]

    def expect(self, string: str) -> Token:
        if self.tok[self.ind].string == string:
            self.ind += 1
            return self.tok[self.ind - 1]
        else:
            self.parse_error()

    def expect_type(self, typ: type) -> Token:
        if isinstance(self.current_token(), typ):
            self.ind += 1
            return self.tok[self.ind - 1]
        else:
            self.parse_error()

    def current_token(self) -> Token:
        return self.tok[self.ind]

    def next_token(self) -> Optional[Token]:
        if self.ind + 1>= len(self.tok):
            return None
        return self.tok[self.ind + 1]

    def current_token_str(self) -> str:
        return self.current_token().string

    def parse_error(self) -> None:
        raise TypeParseError(self.tok[self.ind], self.ind)


def parse_str_as_type(typestr: str, line: int) -> Type:
    """Parse a type represented as a string.

    Raise TypeParseError on parse error.
    """

    typestr = typestr.strip()
    tokens = lex(typestr, line)[0]
    result, i = parse_type(tokens, 0)
    if i < len(tokens) - 2:
        raise TypeParseError(tokens[i], i)
    return result


def parse_signature(tokens: List[Token]) -> Tuple[CallableType, int]:
    """Parse signature of form (argtype, ...) -> ...

    Return tuple (signature type, token index).
    """
    i = 0
    if tokens[i].string != '(':
        raise TypeParseError(tokens[i], i)
    i += 1
    arg_types = []  # type: List[Type]
    arg_kinds = []  # type: List[int]
    encountered_ellipsis = False
    while tokens[i].string != ')':
        if tokens[i].string == '*':
            arg_kinds.append(nodes.ARG_STAR)
            i += 1
        elif tokens[i].string == '**':
            arg_kinds.append(nodes.ARG_STAR2)
            i += 1
        else:
            arg_kinds.append(nodes.ARG_POS)
        arg, i = parse_type(tokens, i)
        arg_types.append(arg)
        next = tokens[i].string

        # Check for ellipsis. If it exists, assert it's the only arg_type.
        # Disallow '(..., int) -> None' for example.
        if isinstance(arg, EllipsisType):
            encountered_ellipsis = True
        if encountered_ellipsis and len(arg_types) != 1:
            raise TypeParseError(tokens[i], i,
                                 "Ellipses cannot accompany other argument types"
                                 " in function type signature.")

        if next not in ',)':
            raise TypeParseError(tokens[i], i)
        if next == ',':
            i += 1
    i += 1
    if tokens[i].string != '->':
        raise TypeParseError(tokens[i], i)
    i += 1
    ret_type, i = parse_type(tokens, i)
    return CallableType(arg_types,
                        arg_kinds,
                        [None] * len(arg_types),
                        ret_type, None,
                        is_ellipsis_args=encountered_ellipsis), i
