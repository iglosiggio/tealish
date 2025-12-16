import inspect
from typing import List, Dict, Union, Tuple
from .base import BaseNode
from .nodes import Node, Program
from .utils import TealishMap
from .types import AVMType, _structs


from puya.parse import SourceLocation
from puya.awst.nodes import Contract, ContractMethod, Block, MethodDocumentation, IfElse, NumericComparison, NumericComparisonExpression, IntrinsicCall, IntegerConstant, AppStateExpression, AssignmentExpression, BytesConstant, BytesEncoding, ReinterpretCast, AssertExpression, BytesComparisonExpression, VarExpression, EqualityComparison, UInt64BinaryOperator, UInt64BinaryOperation, SubmitInnerTransaction, CreateInnerTransaction, AppStorageDefinition, AppStorageKind
from puya.program_refs import ContractReference
from puya.awst.wtypes import bytes_wtype, uint64_wtype, state_key, void_wtype, WInnerTransactionFields
from puya.awst.txn_fields import TxnField

class TealWriter:
    def __init__(self) -> None:
        self.level: int = 0
        self.output: List[str] = []
        self.source_map: Dict[int, int] = {}
        self.current_output_line = 1
        self.current_input_line = 1

    def write(
        self, parent: BaseNode, node_or_teal: Union[BaseNode, str], one_line=False
    ) -> None:
        if one_line:
            w = OneLineTealWriter()
            node_or_teal.write_teal(w)
            self.write(parent, w.teal)
            return
        parent._teal = []
        if isinstance(node_or_teal, BaseNode):
            node = node_or_teal
            i = len(self.output)
            node.write_teal(self)
            parent._teal += self.output[i:]
        elif isinstance(node_or_teal, str):
            teal = node_or_teal
            prefix = (" " * 4) * self.level
            teal = prefix + teal
            if " //" in teal.strip():
                teal, comment = teal.split("//", 1)
                teal = teal.ljust(60) + "//" + comment
            parent._teal.append(teal)
            self.output.append(teal)
            if hasattr(parent, "line_no"):
                self.current_input_line = parent.line_no
            self.source_map[self.current_output_line] = self.current_input_line
            self.current_output_line += 1
        elif isinstance(node_or_teal, list):
            teal_ops = node_or_teal
            if teal_ops[-1].strip().startswith("//"):
                teal = "; ".join(teal_ops[:-1]) + teal_ops[-1]
            else:
                teal = "; ".join(teal_ops)
            self.write(parent, teal)
        else:
            raise Exception(
                "Expected BaseNode or str type as second argument of `write` function"
            )


class OneLineTealWriter:
    def __init__(self) -> None:
        self.teal = []

    def write(self, parent, node_or_teal):
        if isinstance(node_or_teal, BaseNode):
            node_or_teal.write_teal(self)
        elif isinstance(node_or_teal, list):
            self.teal += node_or_teal
        else:
            teal = node_or_teal.split("//", 1)[0]
            self.teal.append(teal)

    @property
    def output(self):
        return "; ".join(self.teal)


class TealishCompiler:
    def __init__(self, source_lines: List[str]) -> None:
        self.source_lines = source_lines
        self.output: List[str] = []
        self.source_map: Dict[int, int] = {}
        self.current_output_line = 1
        self.level = 0
        self.line_no = 0
        self.nodes: List[Node] = []
        self.conditional_count = 0
        self.error_messages: Dict[int, str] = {}
        self.max_slot = 0
        self.writer = TealWriter()
        self.processed = False
        self.awsts = []
        self.line_nodes = {}
        self.use_inner_txns_macro = None

    def consume_line(self) -> str:
        if self.line_no == len(self.source_lines):
            # TODO: this and the func below are Optional[str] but
            # nodes.py uses them heavily and dont
            # check the type is not None
            return  # type: ignore
        line = self.source_lines[self.line_no].strip()
        # strip out inline comments
        if not line.startswith("#"):
            line = line.split("#")[0]
        self.line_no += 1
        return line

    def peek(self) -> str:
        if self.line_no == len(self.source_lines):
            # TODO: see above
            return  # type: ignore
        return self.source_lines[self.line_no].strip()

    def write(self, lines: Union[str, List[str]] = "", line_no: int = 0) -> None:
        prefix = "  " * self.level
        if type(lines) is str:
            lines = [lines]
        for s in lines:
            self.output.append(prefix + s)
            # print(self.current_output_line, self.output[-1])
            self.source_map[self.current_output_line] = line_no
            self.current_output_line += 1

    def parse(self) -> None:
        node = Program.consume(self, None)
        self.nodes.append(node)

    def process(self) -> None:
        for node in self.nodes:
            try:
                node.process()
            except Exception as e:
                node = inspect.trace()[-1].frame.f_locals['self']
                print(node.line_no, node.line)
                raise e
        self.processed = True

    def build_awsts(self) -> None:
        awsts = []
        for node in self.nodes:
            try:
                awsts.append(node.visit(CompilerVisitor()))
            except Exception as e:
                node = inspect.trace()[-1].frame.f_locals['self']
                print(node.line_no, node.line)
                raise e
        self.awsts = awsts

    def compile(self) -> List[str]:
        if not self.nodes:
            self.parse()
        if not self.processed:
            self.process()
        if not self.awsts:
            self.build_awsts()
        self.compile_awsts()
        self.source_map = self.writer.source_map
        self.output = self.writer.output
        return self.writer.output

    def reformat(self) -> str:
        if not self.nodes:
            self.parse()
        if not self.processed:
            self.process()
        return self.nodes[0].tealish()

    def get_map(self) -> TealishMap:
        map = TealishMap()
        map.teal_tealish = dict(self.source_map)
        map.errors = dict(self.error_messages)
        return map

    def get_structs(self):
        return dict(_structs)

    def compile_awsts(self) -> None:
        from puya.compile import awst_to_teal
        from puya.errors import log_exceptions
        from puya.log import logging_context
        from puya.options import PuyaOptions
        from pathlib import Path

        options = PuyaOptions(output_teal=True,
                              output_ssa_ir=True,
                              output_optimization_ir=True,
                              output_destructured_ir=True,
                              output_memory_ir=True,
                              output_teal_intermediates=True,
                              optimization_level=2)
        compilation_set = { contract_ref: Path(".") }
        sources_by_path = { Path("."): None }

        with logging_context() as log_ctx, log_exceptions():
            teal = awst_to_teal(
                log_ctx, options, compilation_set, sources_by_path, self.awsts
            )
            log_ctx.exit_if_errors()

nowhere = SourceLocation(file=None, line=1)
contract_ref = ContractReference("test")

class CompilerVisitor:

    def __init__(self):
        self.ident_level = 0

    def print(self, *args): print(*args)

    def accept(self, node):
        return node.visit(self)

    def accept_nodes(self, nodes):
        return [awst_node for node in nodes if (awst_node := self.accept(node))]

    def visit_program(self, program, nodes):
        body = self.accept_nodes(nodes)
        code = ContractMethod(nowhere, [], uint64_wtype, Block(nowhere, body=body), MethodDocumentation(), cref=contract_ref, member_name="main", arc4_method_config=None)
        app_state = []
        return Contract(nowhere, id=contract_ref, name="test-contract", description=None, method_resolution_order=[], approval_program=code, clear_program=code, methods=[], app_state=app_state, state_totals=None, reserved_scratch_space=set(), avm_version=None)

    def visit_version(self, version): pass

    def visit_blank(self, blank): pass

    def visit_comment(self, comment): pass

    def visit_if(self, if_, condition, then, elifs, else_):
        if if_.modifier is not None:
            raise NotImplementedError
        awst_else = self.accept(else_) if if_.else_ is not None else None
        for elif_ in reversed(elifs):
            awst_else = Block(nowhere, body=[IfElse(nowhere, self.accept(elif_.condition), Block(nowhere, body=self.accept_nodes(elif_.child_nodes)), awst_else)])
        return IfElse(nowhere, self.accept(condition), self.accept(then), awst_else)

    def visit_binop(self, binop, a, b):
        lhs = self.accept(a)
        rhs = self.accept(b)
        if binop.op in NumericComparison and a.type.avm_type is AVMType.int and b.type.avm_type is AVMType.int:
            return NumericComparisonExpression(nowhere, lhs, NumericComparison(binop.op), rhs)
        elif binop.op in EqualityComparison and a.type.avm_type is AVMType.bytes and b.type.avm_type is AVMType.bytes:
            return BytesComparisonExpression(nowhere, lhs, EqualityComparison(binop.op), rhs)
        elif binop.op in UInt64BinaryOperator and a.type.avm_type is AVMType.int and b.type.avm_type is AVMType.int:
            return UInt64BinaryOperation(nowhere, lhs, UInt64BinaryOperator(binop.op), rhs)
        else:
            raise NotImplementedError(binop.op)

    def visit_txn_field(self, txn_field):
        return IntrinsicCall(nowhere, self.to_wtype(txn_field.type), op_code="txn", immediates=[txn_field.field])

    def visit_integer(self, integer):
        return IntegerConstant(nowhere, wtype=uint64_wtype, value=integer.value)

    def visit_if_then(self, if_then, body):
        return Block(nowhere, body=self.accept_nodes(body))

    def visit_op_call(self, op_call, args):
        if op_call.name == "app_global_put":
            var_name, var_value = self.accept_nodes(args)
            var_name_cast = ReinterpretCast(nowhere, state_key, var_name)
            global_var = AppStateExpression(nowhere, var_value.wtype, var_name_cast, None)
            return AssignmentExpression(nowhere, global_var, var_value)
        elif op_call.name == "app_global_get":
            var_name, = self.accept_nodes(args)
            var_name_cast = ReinterpretCast(nowhere, state_key, var_name)
            #FIXME: We need an any type!
            return AppStateExpression(nowhere, uint64_wtype, var_name_cast, None)
        raise NotImplementedError(op_call.name)

    def visit_bytes(self, bytes):
        return BytesConstant(nowhere, value=bytes.value.encode('utf-8'), encoding=BytesEncoding.utf8)

    def visit_exit(self, exit, expr):
        result = self.accept(expr)
        return IntrinsicCall(nowhere, void_wtype, op_code="return", stack_args=[result], immediates=[])

    def visit_enum(self, enum):
        wtype = self.to_wtype(enum.type)
        if wtype is bytes_wtype:
            return BytesConstant(nowhere, value=enum.value.encode('utf-8'), encoding=BytesEncoding.utf8)
        elif wtype is uint64_wtype:
            return IntegerConstant(nowhere, wtype=uint64_wtype, value=enum.value)
        else:
            raise NotImplementedError

    def visit_assert(self, assert_, expr):
        return AssertExpression(nowhere, self.accept(expr), assert_.message)

    def visit_global_field(self, global_field):
        return IntrinsicCall(nowhere, self.to_wtype(global_field.type), op_code="global", immediates=[global_field.field])

    def visit_var_declaration(self, var_declaration, initializer):
        if initializer is not None:
            wtype = self.to_wtype(var_declaration.var.tealish_type)
            var = VarExpression(nowhere, wtype, var_declaration.name.value)
            value = self.accept(initializer)
            return AssignmentExpression(nowhere, var, value)

    def visit_assignment(self, assignment, expr):
        assert len(assignment.vars) == 1
        wtype = self.to_wtype(expr.type)
        var = VarExpression(nowhere, wtype, assignment.vars[0].name)
        value = self.accept(expr)
        return AssignmentExpression(nowhere, var, value)

    def visit_variable(self, variable):
        wtype = self.to_wtype(variable.var.tealish_type)
        return VarExpression(nowhere, wtype, variable.var.name)

    def visit_inner_txn(self, inner_txn, inner_txn_field_setters):
        fields = {
            getattr(TxnField, inner_txn_field_setter.field_name): self.accept(inner_txn_field_setter.expression)
            for inner_txn_field_setter in inner_txn_field_setters
        }
        itxn = CreateInnerTransaction(nowhere, WInnerTransactionFields(None), fields)
        return SubmitInnerTransaction(nowhere, [itxn])

    def visit_inner_txn_field_setter(self, inner_txn_field_setter, expr):
        raise NotImplementedError("must not implement")

    def visit_elif(self, elif_, condition, nodes):
        raise NotImplementedError("must not implement")

    def to_wtype(self, tealish_type):
        if tealish_type.avm_type is AVMType.any:
            raise NotImplementedError
        if tealish_type.avm_type is AVMType.bytes:
            return bytes_wtype
        if tealish_type.avm_type is AVMType.int:
            return uint64_wtype
        if tealish_type.avm_type is AVMType.none:
            raise NotImplementedError


def compile_program(source: str) -> Tuple[List[str], TealishMap]:
    source_lines = source.split("\n")
    compiler = TealishCompiler(source_lines)
    teal = compiler.compile()
    return teal, compiler.get_map()


def reformat_program(source: str) -> str:
    source_lines = source.split("\n")
    compiler = TealishCompiler(source_lines)
    output = compiler.reformat()
    output = output.strip() + "\n"
    return output


def inspect_program(source: str):
    source_lines = source.split("\n")
    compiler = TealishCompiler(source_lines)
    compiler.compile()
    structs = compiler.get_structs()
    structs_output = {}
    for s in structs:
        fields = [(name, structs[s].fields[name]) for name in structs[s].fields]
        structs_output[s] = {
            "size": structs[s].size,
            "fields": {
                name: {"type": str(f.tealish_type), "size": f.size, "offset": f.offset}
                for name, f in fields
            },
        }
    output = {
        "structs": structs_output,
    }
    return output
