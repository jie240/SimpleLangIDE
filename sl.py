#!/usr/bin/env python3
# sl.py - SimpleLang 语言环境
# 用法: python sl.py              -> REPL 交互模式
#       python sl.py file.sl      -> 运行脚本
#       python sl.py -c "代码"    -> 执行代码字符串
#       python sl.py -v           -> 查看版本

import sys
import os
import re
import json
import hashlib
import base64
import urllib.request
import urllib.error
import sqlite3
import datetime
import math
import random
import time

__version__ = "2.0.0"

# ==================== 异常 ====================
class LangError(Exception):
    def __init__(self, msg, line=0, col=0):
        super().__init__(f"[行 {line}, 列 {col}] {msg}")

class BreakException(Exception):
    pass

class ContinueException(Exception):
    pass

class ReturnException(Exception):
    def __init__(self, value):
        self.value = value

# ==================== 词法分析器 ====================
class Token:
    __slots__ = ('type', 'value', 'line', 'col')
    def __init__(self, type_, value, line, col):
        self.type = type_
        self.value = value
        self.line = line
        self.col = col

    def __repr__(self):
        return f"Token({self.type}, {repr(self.value)})"

class Lexer:
    def __init__(self, code):
        self.code = code
        self.pos = 0
        self.line = 1
        self.col = 1
        self.tokens = []

    def peek(self):
        if self.pos + 1 < len(self.code):
            return self.code[self.pos + 1]
        return None

    def advance(self, steps=1):
        for _ in range(steps):
            self.pos += 1
            self.col += 1

    def tokenize(self):
        while self.pos < len(self.code):
            ch = self.code[self.pos]

            # 空白字符
            if ch in ' \t\r':
                self.advance()
                continue

            # 换行
            if ch == '\n':
                self.line += 1
                self.col = 1
                self.advance()
                continue

            # 单行注释 //
            if ch == '/' and self.peek() == '/':
                self.advance(2)
                while self.pos < len(self.code) and self.code[self.pos] != '\n':
                    self.advance()
                continue

            # 多行注释 /* */
            if ch == '/' and self.peek() == '*':
                self.advance(2)
                while self.pos < len(self.code):
                    if self.code[self.pos] == '*' and self.peek() == '/':
                        self.advance(2)
                        break
                    if self.code[self.pos] == '\n':
                        self.line += 1
                        self.col = 1
                    self.advance()
                continue

            # 数字（支持浮点数）
            if ch.isdigit():
                num_str = ''
                is_float = False
                while self.pos < len(self.code):
                    cur = self.code[self.pos]
                    if cur.isdigit():
                        num_str += cur
                        self.advance()
                    elif cur == '.' and not is_float:
                        is_float = True
                        num_str += cur
                        self.advance()
                    else:
                        break
                value = float(num_str) if is_float else int(num_str)
                self.tokens.append(Token('NUMBER', value, self.line, self.col))
                continue

            # 标识符和关键字
            if ch.isalpha() or ch == '_':
                ident = ''
                while self.pos < len(self.code) and (self.code[self.pos].isalnum() or self.code[self.pos] == '_'):
                    ident += self.code[self.pos]
                    self.advance()

                keywords = {
                    'var': 'VAR',
                    'if': 'IF',
                    'else': 'ELSE',
                    'while': 'WHILE',
                    'func': 'FUNC',
                    'return': 'RETURN',
                    'print': 'PRINT',
                    'input': 'INPUT',
                    'input_str': 'INPUT_STR',
                    'for': 'FOR',
                    'in': 'IN',
                    'break': 'BREAK',
                    'continue': 'CONTINUE',
                    'import': 'IMPORT',
                    'try': 'TRY',
                    'catch': 'CATCH',
                    'null': 'NULL',
                    'true': 'TRUE',
                    'false': 'FALSE'
                }

                if ident == 'true':
                    self.tokens.append(Token('TRUE', True, self.line, self.col))
                elif ident == 'false':
                    self.tokens.append(Token('FALSE', False, self.line, self.col))
                elif ident == 'null':
                    self.tokens.append(Token('NULL', None, self.line, self.col))
                else:
                    token_type = keywords.get(ident, 'IDENTIFIER')
                    self.tokens.append(Token(token_type, ident, self.line, self.col))
                continue

            # 字符串
            if ch in ('"', "'"):
                quote = ch
                self.advance()
                string = ''
                while self.pos < len(self.code) and self.code[self.pos] != quote:
                    if self.code[self.pos] == '\\':
                        self.advance()
                        if self.pos < len(self.code):
                            esc = {'"': '"', "'": "'", 'n': '\n', 'r': '\r', 't': '\t', '\\': '\\'}
                            string += esc.get(self.code[self.pos], self.code[self.pos])
                            self.advance()
                        continue
                    if self.code[self.pos] == '\n':
                        self.line += 1
                        self.col = 1
                    string += self.code[self.pos]
                    self.advance()
                if self.pos < len(self.code):
                    self.advance()
                self.tokens.append(Token('STRING', string, self.line, self.col))
                continue

            # 双字符运算符
            two_char = {
                '==': 'EQ', '!=': 'NE', '<=': 'LE', '>=': 'GE',
                '&&': 'AND', '||': 'OR', '++': 'INC', '--': 'DEC',
                '+=': 'PLUS_ASSIGN', '-=': 'MINUS_ASSIGN',
                '*=': 'MUL_ASSIGN', '/=': 'DIV_ASSIGN', '%=': 'MOD_ASSIGN'
            }
            if self.pos + 1 < len(self.code):
                pair = ch + self.peek()
                if pair in two_char:
                    self.tokens.append(Token(two_char[pair], pair, self.line, self.col))
                    self.advance(2)
                    continue

            # 单字符运算符
            single = {
                '+': 'PLUS', '-': 'MINUS', '*': 'MUL', '/': 'DIV', '%': 'MOD',
                '=': 'ASSIGN', '!': 'NOT', '<': 'LT', '>': 'GT',
                '(': 'LPAREN', ')': 'RPAREN', '[': 'LBRACKET', ']': 'RBRACKET',
                '{': 'LBRACE', '}': 'RBRACE', ';': 'SEMICOLON', ',': 'COMMA',
                '.': 'DOT', ':': 'COLON'
            }
            if ch in single:
                self.tokens.append(Token(single[ch], ch, self.line, self.col))
                self.advance()
                continue

            raise LangError(f"非法字符 '{ch}'", self.line, self.col)

        self.tokens.append(Token('EOF', '', self.line, self.col))
        return self.tokens

# ==================== AST 节点 ====================
class Program:
    def __init__(self, statements):
        self.statements = statements

class Block:
    def __init__(self, statements):
        self.statements = statements

class VarDecl:
    def __init__(self, name, init_expr, is_array=False, size_expr=None, is_dict=False):
        self.name = name
        self.init_expr = init_expr
        self.is_array = is_array
        self.size_expr = size_expr
        self.is_dict = is_dict

class Assign:
    def __init__(self, target, expr, op='='):
        self.target = target
        self.expr = expr
        self.op = op

class ArrayAccess:
    def __init__(self, name, index_expr):
        self.name = name
        self.index_expr = index_expr

class DictAccess:
    def __init__(self, name, key):
        self.name = name
        self.key = key

class MemberAccess:
    def __init__(self, obj, member):
        self.obj = obj
        self.member = member

class IfStmt:
    def __init__(self, cond, then_body, else_body=None):
        self.cond = cond
        self.then_body = then_body
        self.else_body = else_body

class WhileStmt:
    def __init__(self, cond, body):
        self.cond = cond
        self.body = body

class ForStmt:
    def __init__(self, init, cond, update, body):
        self.init = init
        self.cond = cond
        self.update = update
        self.body = body

class ForInStmt:
    def __init__(self, var_name, iterable, body):
        self.var_name = var_name
        self.iterable = iterable
        self.body = body

class BreakStmt:
    pass

class ContinueStmt:
    pass

class ReturnStmt:
    def __init__(self, expr=None):
        self.expr = expr

class FuncDef:
    def __init__(self, name, params, body):
        self.name = name
        self.params = params
        self.body = body

class FuncCall:
    def __init__(self, name, args):
        self.name = name
        self.args = args

class MethodCall:
    def __init__(self, obj, method, args):
        self.obj = obj
        self.method = method
        self.args = args

class PrintStmt:
    def __init__(self, exprs):
        self.exprs = exprs

class InputStmt:
    def __init__(self, var_name, as_str=False):
        self.var_name = var_name
        self.as_str = as_str

class DictLiteral:
    def __init__(self, pairs):
        self.pairs = pairs  # list of (key, value) tuples

class ArrayLiteral:
    def __init__(self, elements):
        self.elements = elements

class BinaryOp:
    def __init__(self, left, op, right):
        self.left = left
        self.op = op
        self.right = right

class UnaryOp:
    def __init__(self, op, expr):
        self.op = op
        self.expr = expr

class Variable:
    def __init__(self, name):
        self.name = name

class Number:
    def __init__(self, value):
        self.value = value

class StringLiteral:
    def __init__(self, value):
        self.value = value

class BooleanLiteral:
    def __init__(self, value):
        self.value = value

class NullLiteral:
    pass

class ImportStmt:
    def __init__(self, module_name):
        self.module_name = module_name

class TryCatchStmt:
    def __init__(self, try_body, catch_var, catch_body):
        self.try_body = try_body
        self.catch_var = catch_var
        self.catch_body = catch_body

# ==================== 语法分析器 ====================
class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def current(self):
        return self.tokens[self.pos]

    def eat(self, type_):
        tok = self.current()
        if tok.type == type_:
            self.pos += 1
            return tok
        raise LangError(
            f"期待 {type_}, 实际得到 {tok.type} ('{tok.value}')",
            tok.line, tok.col
        )

    def parse(self):
        stmts = []
        while self.current().type != 'EOF':
            stmt = self.parse_statement()
            if stmt is not None:
                stmts.append(stmt)
        return Program(stmts)

    def parse_statement(self):
        tok = self.current()

        if tok.type == 'VAR':
            return self.parse_var_decl()
        if tok.type == 'IF':
            return self.parse_if()
        if tok.type == 'WHILE':
            return self.parse_while()
        if tok.type == 'FOR':
            return self.parse_for()
        if tok.type == 'BREAK':
            self.eat('BREAK')
            self.eat('SEMICOLON')
            return BreakStmt()
        if tok.type == 'CONTINUE':
            self.eat('CONTINUE')
            self.eat('SEMICOLON')
            return ContinueStmt()
        if tok.type == 'FUNC':
            return self.parse_func_def()
        if tok.type == 'RETURN':
            return self.parse_return()
        if tok.type == 'PRINT':
            return self.parse_print()
        if tok.type == 'IMPORT':
            return self.parse_import()
        if tok.type == 'TRY':
            return self.parse_try_catch()
        if tok.type in ('INPUT', 'INPUT_STR'):
            as_str = (tok.type == 'INPUT_STR')
            self.eat(tok.type)
            name = self.eat('IDENTIFIER').value
            self.eat('SEMICOLON')
            return InputStmt(name, as_str)
        if tok.type == 'LBRACE':
            return self.parse_block()
        if tok.type == 'SEMICOLON':
            self.eat('SEMICOLON')
            return None
        if tok.type == 'IDENTIFIER':
            return self._parse_identifier_statement()

        raise LangError(f"无效的语句开始: {tok.type}", tok.line, tok.col)

    def _parse_identifier_statement(self):
        name = self.eat('IDENTIFIER').value
        expr = Variable(name)

        # 处理链式访问: obj.member, obj[index], obj.method()
        while self.current().type in ('DOT', 'LBRACKET'):
            if self.current().type == 'DOT':
                self.eat('DOT')
                member = self.eat('IDENTIFIER').value
                if self.current().type == 'LPAREN':
                    args = self.parse_args()
                    expr = MethodCall(expr, member, args)
                else:
                    expr = MemberAccess(expr, member)
            elif self.current().type == 'LBRACKET':
                self.eat('LBRACKET')
                if self.current().type == 'STRING':
                    key = self.eat('STRING').value
                    expr = DictAccess(expr, StringLiteral(key))
                else:
                    idx = self.parse_expression()
                    expr = ArrayAccess(expr, idx)
                self.eat('RBRACKET')

        # 赋值运算
        assign_ops = {
            'ASSIGN': '=',
            'PLUS_ASSIGN': '+=',
            'MINUS_ASSIGN': '-=',
            'MUL_ASSIGN': '*=',
            'DIV_ASSIGN': '/=',
            'MOD_ASSIGN': '%='
        }
        if self.current().type in assign_ops:
            op = assign_ops[self.current().type]
            self.eat(self.current().type)
            val = self.parse_expression()
            self.eat('SEMICOLON')
            return Assign(expr, val, op)

        # 函数调用
        if isinstance(expr, Variable) and self.current().type == 'LPAREN':
            args = self.parse_args()
            self.eat('SEMICOLON')
            return FuncCall(expr.name, args)

        self.eat('SEMICOLON')
        return expr

    def parse_args(self):
        args = []
        self.eat('LPAREN')
        if self.current().type != 'RPAREN':
            args.append(self.parse_expression())
            while self.current().type == 'COMMA':
                self.eat('COMMA')
                args.append(self.parse_expression())
        self.eat('RPAREN')
        return args

    def parse_var_decl(self):
        self.eat('VAR')
        name = self.eat('IDENTIFIER').value

        is_array = False
        is_dict = False
        size_expr = None

        if self.current().type == 'LBRACKET':
            self.eat('LBRACKET')
            if self.current().type == 'RBRACKET':
                is_dict = True
            else:
                is_array = True
                size_expr = self.parse_expression()
            self.eat('RBRACKET')

        init_expr = None
        if self.current().type == 'ASSIGN':
            self.eat('ASSIGN')
            if is_dict or self.current().type == 'LBRACE':
                init_expr = self.parse_dict_literal()
            elif self.current().type == 'LBRACKET':
                init_expr = self.parse_array_literal()
            else:
                init_expr = self.parse_expression()

        self.eat('SEMICOLON')
        return VarDecl(name, init_expr, is_array, size_expr, is_dict)

    def parse_dict_literal(self):
        pairs = []
        self.eat('LBRACE')
        while self.current().type != 'RBRACE':
            if self.current().type == 'STRING':
                key = self.eat('STRING').value
            else:
                key = self.eat('IDENTIFIER').value
            self.eat('COLON')
            value = self.parse_expression()
            pairs.append((key, value))
            if self.current().type == 'COMMA':
                self.eat('COMMA')
        self.eat('RBRACE')
        return DictLiteral(pairs)

    def parse_array_literal(self):
        elements = []
        self.eat('LBRACKET')
        while self.current().type != 'RBRACKET':
            elements.append(self.parse_expression())
            if self.current().type == 'COMMA':
                self.eat('COMMA')
        self.eat('RBRACKET')
        return ArrayLiteral(elements)

    def parse_if(self):
        self.eat('IF')
        self.eat('LPAREN')
        cond = self.parse_expression()
        self.eat('RPAREN')
        then_body = self.parse_statement()
        else_body = None
        if self.current().type == 'ELSE':
            self.eat('ELSE')
            if self.current().type == 'IF':
                else_body = self.parse_if()
            else:
                else_body = self.parse_statement()
        return IfStmt(cond, then_body, else_body)

    def parse_while(self):
        self.eat('WHILE')
        self.eat('LPAREN')
        cond = self.parse_expression()
        self.eat('RPAREN')
        body = self.parse_statement()
        return WhileStmt(cond, body)

    def parse_for(self):
        self.eat('FOR')
        self.eat('LPAREN')

        # 检查是否为 for-in 循环
        saved_pos = self.pos
        if self.current().type == 'VAR' and self.tokens[saved_pos + 1].type == 'IDENTIFIER':
            look = saved_pos + 2
            while look < len(self.tokens) and self.tokens[look].type not in ('IN', 'SEMICOLON', 'EOF'):
                look += 1
            if look < len(self.tokens) and self.tokens[look].type == 'IN':
                self.eat('VAR')
                var_name = self.eat('IDENTIFIER').value
                self.eat('IN')
                iterable = self.parse_expression()
                self.eat('RPAREN')
                body = self.parse_statement()
                return ForInStmt(var_name, iterable, body)

        # 传统 for 循环
        init = None
        if self.current().type != 'SEMICOLON':
            if self.current().type == 'VAR':
                init = self.parse_var_decl()
            else:
                init = self.parse_expression()
        self.eat('SEMICOLON')

        cond = None
        if self.current().type != 'SEMICOLON':
            cond = self.parse_expression()
        self.eat('SEMICOLON')

        update = None
        if self.current().type != 'RPAREN':
            update = self.parse_expression()
        self.eat('RPAREN')

        body = self.parse_statement()
        return ForStmt(init, cond, update, body)

    def parse_func_def(self):
        self.eat('FUNC')
        name = self.eat('IDENTIFIER').value
        self.eat('LPAREN')
        params = []
        if self.current().type == 'IDENTIFIER':
            params.append(self.eat('IDENTIFIER').value)
            while self.current().type == 'COMMA':
                self.eat('COMMA')
                params.append(self.eat('IDENTIFIER').value)
        self.eat('RPAREN')
        body = self.parse_block()
        return FuncDef(name, params, body)

    def parse_return(self):
        self.eat('RETURN')
        expr = None
        if self.current().type != 'SEMICOLON':
            expr = self.parse_expression()
        self.eat('SEMICOLON')
        return ReturnStmt(expr)

    def parse_print(self):
        self.eat('PRINT')
        exprs = [self.parse_expression()]
        while self.current().type == 'COMMA':
            self.eat('COMMA')
            exprs.append(self.parse_expression())
        self.eat('SEMICOLON')
        return PrintStmt(exprs)

    def parse_import(self):
        self.eat('IMPORT')
        module = self.eat('STRING').value
        self.eat('SEMICOLON')
        return ImportStmt(module)

    def parse_try_catch(self):
        self.eat('TRY')
        try_body = self.parse_block()
        self.eat('CATCH')
        self.eat('LPAREN')
        catch_var = self.eat('IDENTIFIER').value
        self.eat('RPAREN')
        catch_body = self.parse_block()
        return TryCatchStmt(try_body, catch_var, catch_body)

    def parse_block(self):
        self.eat('LBRACE')
        stmts = []
        while self.current().type != 'RBRACE':
            stmt = self.parse_statement()
            if stmt is not None:
                stmts.append(stmt)
        self.eat('RBRACE')
        return Block(stmts)

    # 运算符优先级解析
    def parse_expression(self):
        return self.parse_logical_or()

    def parse_logical_or(self):
        left = self.parse_logical_and()
        while self.current().type == 'OR':
            op = self.eat('OR').value
            right = self.parse_logical_and()
            left = BinaryOp(left, op, right)
        return left

    def parse_logical_and(self):
        left = self.parse_equality()
        while self.current().type == 'AND':
            op = self.eat('AND').value
            right = self.parse_equality()
            left = BinaryOp(left, op, right)
        return left

    def parse_equality(self):
        left = self.parse_comparison()
        while self.current().type in ('EQ', 'NE'):
            op = self.eat(self.current().type).value
            right = self.parse_comparison()
            left = BinaryOp(left, op, right)
        return left

    def parse_comparison(self):
        left = self.parse_additive()
        while self.current().type in ('LT', 'GT', 'LE', 'GE'):
            op = self.eat(self.current().type).value
            right = self.parse_additive()
            left = BinaryOp(left, op, right)
        return left

    def parse_additive(self):
        left = self.parse_multiplicative()
        while self.current().type in ('PLUS', 'MINUS'):
            op = self.eat(self.current().type).value
            right = self.parse_multiplicative()
            left = BinaryOp(left, op, right)
        return left

    def parse_multiplicative(self):
        left = self.parse_unary()
        while self.current().type in ('MUL', 'DIV', 'MOD'):
            op = self.eat(self.current().type).value
            right = self.parse_unary()
            left = BinaryOp(left, op, right)
        return left

    def parse_unary(self):
        if self.current().type in ('NOT', 'MINUS', 'INC', 'DEC'):
            op = self.eat(self.current().type).value
            expr = self.parse_unary()
            return UnaryOp(op, expr)
        return self.parse_primary()

    def parse_primary(self):
        tok = self.current()

        if tok.type == 'NUMBER':
            self.eat('NUMBER')
            return Number(tok.value)
        if tok.type == 'STRING':
            self.eat('STRING')
            return StringLiteral(tok.value)
        if tok.type == 'TRUE':
            self.eat('TRUE')
            return BooleanLiteral(True)
        if tok.type == 'FALSE':
            self.eat('FALSE')
            return BooleanLiteral(False)
        if tok.type == 'NULL':
            self.eat('NULL')
            return NullLiteral()
        if tok.type == 'LBRACKET':
            return self.parse_array_literal()
        if tok.type == 'LBRACE':
            return self.parse_dict_literal()

        if tok.type == 'IDENTIFIER':
            name = self.eat('IDENTIFIER').value
            expr = Variable(name)

            # 链式访问
            while self.current().type in ('DOT', 'LBRACKET'):
                if self.current().type == 'DOT':
                    self.eat('DOT')
                    member = self.eat('IDENTIFIER').value
                    if self.current().type == 'LPAREN':
                        args = self.parse_args()
                        expr = MethodCall(expr, member, args)
                    else:
                        expr = MemberAccess(expr, member)
                elif self.current().type == 'LBRACKET':
                    self.eat('LBRACKET')
                    if self.current().type == 'STRING':
                        key = self.eat('STRING').value
                        expr = DictAccess(expr, StringLiteral(key))
                    else:
                        idx = self.parse_expression()
                        expr = ArrayAccess(expr, idx)
                    self.eat('RBRACKET')

            # 函数调用
            if self.current().type == 'LPAREN':
                args = self.parse_args()
                return FuncCall(name, args)

            return expr

        if tok.type == 'LPAREN':
            self.eat('LPAREN')
            expr = self.parse_expression()
            self.eat('RPAREN')
            return expr

        raise LangError(f"意外的符号 {tok.type}", tok.line, tok.col)

# ==================== 标准库 ====================
class StdLib:
    """SimpleLang 标准库"""

    @staticmethod
    def http_get(url, headers=None):
        try:
            req = urllib.request.Request(url)
            if headers and isinstance(headers, dict):
                for k, v in headers.items():
                    req.add_header(k, str(v))
            with urllib.request.urlopen(req, timeout=10) as resp:
                return {'status': resp.status, 'body': resp.read().decode('utf-8', errors='replace')}
        except Exception as e:
            return {'status': 0, 'body': str(e)}

    @staticmethod
    def http_post(url, data, headers=None):
        try:
            data_bytes = str(data).encode('utf-8') if isinstance(data, str) else data
            req = urllib.request.Request(url, data=data_bytes, method='POST')
            if headers and isinstance(headers, dict):
                for k, v in headers.items():
                    req.add_header(k, str(v))
            with urllib.request.urlopen(req, timeout=10) as resp:
                return {'status': resp.status, 'body': resp.read().decode('utf-8', errors='replace')}
        except Exception as e:
            return {'status': 0, 'body': str(e)}

    @staticmethod
    def json_parse(text):
        return json.loads(text)

    @staticmethod
    def json_stringify(obj):
        return json.dumps(obj, ensure_ascii=False, default=str)

    @staticmethod
    def file_read(path):
        try:
            with open(path, 'r', encoding='utf-8') as f:
                return f.read()
        except:
            return None

    @staticmethod
    def file_write(path, content):
        try:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(str(content))
            return True
        except:
            return False

    @staticmethod
    def file_append(path, content):
        try:
            with open(path, 'a', encoding='utf-8') as f:
                f.write(str(content))
            return True
        except:
            return False

    @staticmethod
    def file_exists(path):
        return os.path.exists(path)

    @staticmethod
    def file_delete(path):
        try:
            os.remove(path)
            return True
        except:
            return False

    @staticmethod
    def file_list_dir(path='.'):
        try:
            return os.listdir(path)
        except:
            return []

    @staticmethod
    def file_mkdir(path):
        try:
            os.makedirs(path, exist_ok=True)
            return True
        except:
            return False

    @staticmethod
    def regex_match(pattern, text):
        try:
            return re.findall(pattern, text)
        except:
            return []

    @staticmethod
    def regex_replace(pattern, repl, text):
        try:
            return re.sub(pattern, repl, text)
        except:
            return text

    @staticmethod
    def regex_test(pattern, text):
        try:
            return bool(re.search(pattern, text))
        except:
            return False

    @staticmethod
    def db_open(path):
        try:
            return sqlite3.connect(path)
        except:
            return None

    @staticmethod
    def db_execute(conn, sql, params=None):
        try:
            cur = conn.cursor()
            if params:
                cur.execute(sql, params)
            else:
                cur.execute(sql)
            conn.commit()
            return {'rows': cur.rowcount, 'last_id': cur.lastrowid}
        except Exception as e:
            return {'error': str(e)}

    @staticmethod
    def db_query(conn, sql, params=None):
        try:
            cur = conn.cursor()
            if params:
                cur.execute(sql, params)
            else:
                cur.execute(sql)
            cols = [d[0] for d in cur.description] if cur.description else []
            return [dict(zip(cols, r)) for r in cur.fetchall()]
        except Exception as e:
            return [{'error': str(e)}]

    @staticmethod
    def db_close(conn):
        try:
            conn.close()
            return True
        except:
            return False

    @staticmethod
    def hash_md5(s):
        return hashlib.md5(str(s).encode()).hexdigest()

    @staticmethod
    def hash_sha256(s):
        return hashlib.sha256(str(s).encode()).hexdigest()

    @staticmethod
    def hash_sha1(s):
        return hashlib.sha1(str(s).encode()).hexdigest()

    @staticmethod
    def base64_encode(s):
        return base64.b64encode(str(s).encode()).decode()

    @staticmethod
    def base64_decode(s):
        try:
            return base64.b64decode(s.encode()).decode()
        except:
            return None

    @staticmethod
    def str_split(s, d):
        return s.split(d)

    @staticmethod
    def str_join(d, arr):
        return d.join(str(i) for i in arr)

    @staticmethod
    def str_replace(s, old, new):
        return s.replace(old, new)

    @staticmethod
    def str_contains(s, sub):
        return sub in s

    @staticmethod
    def str_upper(s):
        return s.upper()

    @staticmethod
    def str_lower(s):
        return s.lower()

    @staticmethod
    def str_trim(s):
        return s.strip()

    @staticmethod
    def str_length(s):
        return len(str(s))

    @staticmethod
    def str_substring(s, start, length=None):
        if length is not None:
            return s[start:start + length]
        return s[start:]

    @staticmethod
    def math_abs(x):
        return abs(x)

    @staticmethod
    def math_ceil(x):
        return math.ceil(x)

    @staticmethod
    def math_floor(x):
        return math.floor(x)

    @staticmethod
    def math_round(x):
        return round(x)

    @staticmethod
    def math_sqrt(x):
        return math.sqrt(x)

    @staticmethod
    def math_pow(x, y):
        return math.pow(x, y)

    @staticmethod
    def math_sin(x):
        return math.sin(x)

    @staticmethod
    def math_cos(x):
        return math.cos(x)

    @staticmethod
    def math_random():
        return random.random()

    @staticmethod
    def math_random_int(a, b):
        return random.randint(a, b)

    @staticmethod
    def time_now():
        return time.time()

    @staticmethod
    def time_format(ts, fmt="%Y-%m-%d %H:%M:%S"):
        return datetime.datetime.fromtimestamp(ts).strftime(fmt)

    @staticmethod
    def time_sleep(s):
        time.sleep(s)

    @staticmethod
    def array_push(arr, v):
        arr.append(v)
        return arr

    @staticmethod
    def array_pop(arr):
        if arr:
            return arr.pop()
        return None

    @staticmethod
    def array_shift(arr):
        if arr:
            return arr.pop(0)
        return None

    @staticmethod
    def array_unshift(arr, v):
        arr.insert(0, v)
        return arr

    @staticmethod
    def array_length(arr):
        return len(arr)

    @staticmethod
    def array_join(arr, d):
        return d.join(str(i) for i in arr)

    @staticmethod
    def array_sort(arr):
        arr.sort()
        return arr

    @staticmethod
    def array_reverse(arr):
        arr.reverse()
        return arr

    @staticmethod
    def array_index_of(arr, v):
        try:
            return arr.index(v)
        except:
            return -1

    @staticmethod
    def array_slice(arr, s, e=None):
        if e is not None:
            return arr[s:e]
        return arr[s:]

    @staticmethod
    def dict_keys(d):
        if isinstance(d, dict):
            return list(d.keys())
        return []

    @staticmethod
    def dict_values(d):
        if isinstance(d, dict):
            return list(d.values())
        return []

    @staticmethod
    def dict_has(d, k):
        if isinstance(d, dict):
            return k in d
        return False

    @staticmethod
    def dict_remove(d, k):
        if isinstance(d, dict) and k in d:
            del d[k]
        return d

    @staticmethod
    def type_of(v):
        if v is None:
            return "null"
        if isinstance(v, bool):
            return "bool"
        if isinstance(v, int):
            return "int"
        if isinstance(v, float):
            return "float"
        if isinstance(v, str):
            return "string"
        if isinstance(v, list):
            return "array"
        if isinstance(v, dict):
            return "dict"
        return "object"

    @staticmethod
    def to_int(v):
        try:
            return int(float(v))
        except:
            return 0

    @staticmethod
    def to_float(v):
        try:
            return float(v)
        except:
            return 0.0

    @staticmethod
    def to_str(v):
        return str(v)

    @staticmethod
    def to_bool(v):
        if v is None:
            return False
        if isinstance(v, bool):
            return v
        if isinstance(v, str):
            return v.lower() in ('true', '1', 'yes')
        return bool(v)

# ==================== 解释器 ====================
class Interpreter:
    def __init__(self):
        self.scopes = [{}]
        self.functions = {}
        self.stdlib = StdLib()
        self.imported_modules = {}
        self._last_result = None

    def push_scope(self, d=None):
        self.scopes.append(d if d is not None else {})

    def pop_scope(self):
        if len(self.scopes) > 1:
            self.scopes.pop()

    def get_var(self, name):
        for scope in reversed(self.scopes):
            if name in scope:
                return scope[name]
        if hasattr(self.stdlib, name):
            return getattr(self.stdlib, name)
        raise LangError(f"未定义的变量 '{name}'")

    def set_var(self, name, value):
        for scope in reversed(self.scopes):
            if name in scope:
                scope[name] = value
                return
        self.scopes[0][name] = value

    def interpret(self, node):
        if isinstance(node, Program):
            for stmt in node.statements:
                self.execute(stmt)
        elif isinstance(node, Block):
            for stmt in node.statements:
                self.execute(stmt)

    def execute(self, stmt):
        if stmt is None:
            return

        # 变量声明
        if isinstance(stmt, VarDecl):
            val = None
            if stmt.is_dict:
                if stmt.init_expr is not None:
                    val = self.evaluate(stmt.init_expr)
                else:
                    val = {}
            elif stmt.is_array:
                if stmt.init_expr is not None:
                    val = self.evaluate(stmt.init_expr)
                else:
                    size = int(self.evaluate(stmt.size_expr) if stmt.size_expr else 0)
                    val = [0] * size
            else:
                val = 0
                if stmt.init_expr is not None:
                    val = self.evaluate(stmt.init_expr)
            self.set_var(stmt.name, val)

        # 赋值
        elif isinstance(stmt, Assign):
            val = self.evaluate(stmt.expr)
            if stmt.op != '=':
                old = self.evaluate(stmt.target)
                ops = {
                    '+=': lambda a, b: a + b,
                    '-=': lambda a, b: a - b,
                    '*=': lambda a, b: a * b,
                    '/=': lambda a, b: a / b,
                    '%=': lambda a, b: a % b
                }
                if stmt.op in ops:
                    val = ops[stmt.op](old, val)
            self._set_target(stmt.target, val)

        # if 语句
        elif isinstance(stmt, IfStmt):
            cond = self.evaluate(stmt.cond)
            if cond:
                self.execute(stmt.then_body)
            elif stmt.else_body:
                self.execute(stmt.else_body)

        # while 循环
        elif isinstance(stmt, WhileStmt):
            while self.evaluate(stmt.cond):
                try:
                    self.execute(stmt.body)
                except BreakException:
                    break
                except ContinueException:
                    continue

        # for 循环
        elif isinstance(stmt, ForStmt):
            self.push_scope()
            try:
                if stmt.init:
                    if isinstance(stmt.init, VarDecl):
                        self.execute(stmt.init)
                    else:
                        self.evaluate(stmt.init)
                while stmt.cond is None or self.evaluate(stmt.cond):
                    try:
                        self.execute(stmt.body)
                    except BreakException:
                        break
                    except ContinueException:
                        pass
                    if stmt.update:
                        self.evaluate(stmt.update)
            finally:
                self.pop_scope()

        # for-in 循环
        elif isinstance(stmt, ForInStmt):
            iterable = self.evaluate(stmt.iterable)
            if isinstance(iterable, dict):
                items = iterable.keys()
            elif isinstance(iterable, (list, str)):
                items = iterable
            else:
                items = [iterable]

            for item in items:
                self.push_scope({stmt.var_name: item})
                try:
                    self.execute(stmt.body)
                except BreakException:
                    self.pop_scope()
                    break
                except ContinueException:
                    pass
                finally:
                    if len(self.scopes) > 1:
                        scope = self.scopes.pop()
                        if stmt.var_name in scope:
                            del scope[stmt.var_name]

        elif isinstance(stmt, BreakStmt):
            raise BreakException()
        elif isinstance(stmt, ContinueStmt):
            raise ContinueException()

        # 函数定义
        elif isinstance(stmt, FuncDef):
            self.functions[stmt.name] = (stmt.params, stmt.body)

        # return 语句
        elif isinstance(stmt, ReturnStmt):
            val = self.evaluate(stmt.expr) if stmt.expr else 0
            raise ReturnException(val)

        # print 语句
        elif isinstance(stmt, PrintStmt):
            parts = [str(self.evaluate(e)) for e in stmt.exprs]
            print(''.join(parts))

        # input 语句
        elif isinstance(stmt, InputStmt):
            prompt = ">>> "
            val = input(prompt)
            if not stmt.as_str:
                try:
                    val = float(val) if '.' in val else int(val)
                except:
                    val = 0
            self.set_var(stmt.var_name, val)

        # import 语句
        elif isinstance(stmt, ImportStmt):
            try:
                mod = __import__(stmt.module_name)
                self.imported_modules[stmt.module_name] = mod
                self.set_var(stmt.module_name, mod)
            except ImportError:
                raise LangError(f"无法导入模块 '{stmt.module_name}'")

        # try-catch 语句
        elif isinstance(stmt, TryCatchStmt):
            try:
                self.execute(stmt.try_body)
            except Exception as e:
                self.push_scope({stmt.catch_var: str(e)})
                self.execute(stmt.catch_body)
                self.pop_scope()

        # 表达式语句
        elif isinstance(stmt, (FuncCall, Variable, Number, StringLiteral, BinaryOp, UnaryOp)):
            self._last_result = self.evaluate(stmt)

        # 代码块
        elif isinstance(stmt, Block):
            for s in stmt.statements:
                self.execute(s)

        else:
            self._last_result = self.evaluate(stmt)

    def _set_target(self, target, val):
        if isinstance(target, Variable):
            self.set_var(target.name, val)
        elif isinstance(target, ArrayAccess):
            arr = self._eval_access_name(target.name)
            idx = int(self.evaluate(target.index_expr))
            if 0 <= idx < len(arr):
                arr[idx] = val
            else:
                raise LangError(f"数组索引 {idx} 越界")
        elif isinstance(target, DictAccess):
            d = self._eval_access_name(target.name)
            key = str(self.evaluate(target.key))
            d[key] = val
        elif isinstance(target, MemberAccess):
            obj = self.evaluate(target.obj)
            if isinstance(obj, dict):
                obj[target.member] = val
            else:
                setattr(obj, target.member, val)

    def _eval_access_name(self, name_node):
        if isinstance(name_node, Variable):
            return self.get_var(name_node.name)
        return self.evaluate(name_node)

    def evaluate(self, expr):
        if expr is None:
            return None

        if isinstance(expr, Number):
            return expr.value
        if isinstance(expr, StringLiteral):
            return expr.value
        if isinstance(expr, BooleanLiteral):
            return expr.value
        if isinstance(expr, NullLiteral):
            return None

        if isinstance(expr, Variable):
            return self.get_var(expr.name)

        if isinstance(expr, ArrayLiteral):
            return [self.evaluate(e) for e in expr.elements]

        if isinstance(expr, DictLiteral):
            result = {}
            for k, v in expr.pairs:
                result[str(k)] = self.evaluate(v)
            return result

        if isinstance(expr, ArrayAccess):
            arr = self._eval_access_name(expr.name)
            idx = int(self.evaluate(expr.index_expr))
            if 0 <= idx < len(arr):
                return arr[idx]
            raise LangError(f"数组索引 {idx} 越界 (长度 {len(arr)})")

        if isinstance(expr, DictAccess):
            d = self._eval_access_name(expr.name)
            key = str(self.evaluate(expr.key))
            if isinstance(d, dict):
                return d.get(key, None)
            raise LangError(f"无法访问键 '{key}' (对象不是字典)")

        if isinstance(expr, MemberAccess):
            obj = self.evaluate(expr.obj)
            if isinstance(obj, dict):
                return obj.get(expr.member, None)
            return getattr(obj, expr.member, None)

        if isinstance(expr, MethodCall):
            obj = self.evaluate(expr.obj)
            args = [self.evaluate(a) for a in expr.args]
            if isinstance(obj, dict) and expr.method in obj:
                func = obj[expr.method]
                if callable(func):
                    return func(*args)
            if hasattr(obj, expr.method):
                func = getattr(obj, expr.method)
                if callable(func):
                    return func(*args)
            raise LangError(f"方法 '{expr.method}' 未找到")

        if isinstance(expr, BinaryOp):
            left = self.evaluate(expr.left)
            right = self.evaluate(expr.right)
            op = expr.op

            ops = {
                '+': lambda a, b: a + b,
                '-': lambda a, b: a - b,
                '*': lambda a, b: a * b,
                '/': lambda a, b: a / b if b != 0 else exec('raise LangError("除零错误")'),
                '%': lambda a, b: a % b if b != 0 else exec('raise LangError("模零错误")'),
                '==': lambda a, b: a == b,
                '!=': lambda a, b: a != b,
                '<': lambda a, b: a < b,
                '>': lambda a, b: a > b,
                '<=': lambda a, b: a <= b,
                '>=': lambda a, b: a >= b,
                '&&': lambda a, b: a and b,
                '||': lambda a, b: a or b
            }

            if op in ops:
                try:
                    return ops[op](left, right)
                except ZeroDivisionError:
                    raise LangError("除零错误")

            raise LangError(f"未知运算符: {op}")

        if isinstance(expr, UnaryOp):
            val = self.evaluate(expr.expr)
            if expr.op == '!':
                return not val
            if expr.op == '-':
                return -val
            if expr.op == '++':
                return val + 1
            if expr.op == '--':
                return val - 1

        if isinstance(expr, FuncCall):
            args = [self.evaluate(a) for a in expr.args]
            return self._call_function(expr.name, args)

        return None

    def _call_function(self, name, args):
        # 内置函数
        builtins = {
            'len': lambda: len(args[0]) if args else 0,
            'to_int': lambda: int(float(args[0])),
            'to_float': lambda: float(args[0]),
            'to_str': lambda: str(args[0]),
            'to_bool': lambda: self.stdlib.to_bool(args[0]),
            'type_of': lambda: self.stdlib.type_of(args[0]),
            'range': lambda: list(range(int(args[0]))) if len(args) == 1
            else list(range(int(args[0]), int(args[1]))),
            'print': lambda: print(*args),
            'input': lambda: input(args[0] if args else ''),
        }

        if name in builtins:
            return builtins[name]()

        # 标准库函数
        std_funcs = {
            'http_get': lambda: self.stdlib.http_get(args[0], args[1] if len(args) > 1 else None),
            'http_post': lambda: self.stdlib.http_post(args[0], args[1], args[2] if len(args) > 2 else None),
            'json_parse': lambda: self.stdlib.json_parse(args[0]),
            'json_stringify': lambda: self.stdlib.json_stringify(args[0]),
            'file_read': lambda: self.stdlib.file_read(args[0]),
            'file_write': lambda: self.stdlib.file_write(args[0], args[1]) if len(args) > 1 else False,
            'file_append': lambda: self.stdlib.file_append(args[0], args[1]),
            'file_exists': lambda: self.stdlib.file_exists(args[0]),
            'file_delete': lambda: self.stdlib.file_delete(args[0]),
            'file_list_dir': lambda: self.stdlib.file_list_dir(args[0] if args else '.'),
            'file_mkdir': lambda: self.stdlib.file_mkdir(args[0]),
            'regex_match': lambda: self.stdlib.regex_match(args[0], args[1]),
            'regex_replace': lambda: self.stdlib.regex_replace(args[0], args[1], args[2]) if len(args) > 2 else '',
            'regex_test': lambda: self.stdlib.regex_test(args[0], args[1]),
            'hash_md5': lambda: self.stdlib.hash_md5(args[0]),
            'hash_sha256': lambda: self.stdlib.hash_sha256(args[0]),
            'hash_sha1': lambda: self.stdlib.hash_sha1(args[0]),
            'base64_encode': lambda: self.stdlib.base64_encode(args[0]),
            'base64_decode': lambda: self.stdlib.base64_decode(args[0]),
            'str_split': lambda: self.stdlib.str_split(args[0], args[1]),
            'str_join': lambda: self.stdlib.str_join(args[0], args[1]),
            'str_replace': lambda: self.stdlib.str_replace(args[0], args[1], args[2]) if len(args) > 2 else args[0],
            'str_contains': lambda: self.stdlib.str_contains(args[0], args[1]),
            'str_upper': lambda: self.stdlib.str_upper(args[0]),
            'str_lower': lambda: self.stdlib.str_lower(args[0]),
            'str_trim': lambda: self.stdlib.str_trim(args[0]),
            'str_length': lambda: self.stdlib.str_length(args[0]),
            'str_substring': lambda: self.stdlib.str_substring(args[0], int(args[1]),
                                                               int(args[2]) if len(args) > 2 else None),
            'math_abs': lambda: self.stdlib.math_abs(args[0]),
            'math_ceil': lambda: self.stdlib.math_ceil(args[0]),
            'math_floor': lambda: self.stdlib.math_floor(args[0]),
            'math_round': lambda: self.stdlib.math_round(args[0]),
            'math_sqrt': lambda: self.stdlib.math_sqrt(args[0]),
            'math_pow': lambda: self.stdlib.math_pow(args[0], args[1]),
            'math_sin': lambda: self.stdlib.math_sin(args[0]),
            'math_cos': lambda: self.stdlib.math_cos(args[0]),
            'math_random': lambda: self.stdlib.math_random(),
            'math_random_int': lambda: self.stdlib.math_random_int(int(args[0]), int(args[1])),
            'time_now': lambda: self.stdlib.time_now(),
            'time_format': lambda: self.stdlib.time_format(args[0], args[1] if len(args) > 1 else "%Y-%m-%d %H:%M:%S"),
            'time_sleep': lambda: self.stdlib.time_sleep(args[0]),
            'array_push': lambda: self.stdlib.array_push(args[0], args[1]),
            'array_pop': lambda: self.stdlib.array_pop(args[0]),
            'array_shift': lambda: self.stdlib.array_shift(args[0]),
            'array_unshift': lambda: self.stdlib.array_unshift(args[0], args[1]),
            'array_length': lambda: self.stdlib.array_length(args[0]),
            'array_join': lambda: self.stdlib.array_join(args[0], args[1]),
            'array_sort': lambda: self.stdlib.array_sort(args[0]),
            'array_reverse': lambda: self.stdlib.array_reverse(args[0]),
            'array_index_of': lambda: self.stdlib.array_index_of(args[0], args[1]),
            'array_slice': lambda: self.stdlib.array_slice(args[0], int(args[1]),
                                                           int(args[2]) if len(args) > 2 else None),
            'dict_keys': lambda: self.stdlib.dict_keys(args[0]),
            'dict_values': lambda: self.stdlib.dict_values(args[0]),
            'dict_has': lambda: self.stdlib.dict_has(args[0], args[1]),
            'dict_remove': lambda: self.stdlib.dict_remove(args[0], args[1]),
            'db_open': lambda: self.stdlib.db_open(args[0]),
            'db_execute': lambda: self.stdlib.db_execute(args[0], args[1], args[2] if len(args) > 2 else None),
            'db_query': lambda: self.stdlib.db_query(args[0], args[1], args[2] if len(args) > 2 else None),
            'db_close': lambda: self.stdlib.db_close(args[0]),
        }

        if name in std_funcs:
            return std_funcs[name]()

        # 用户定义函数
        if name in self.functions:
            params, body = self.functions[name]
            if len(params) != len(args):
                raise LangError(f"函数 '{name}' 需要 {len(params)} 个参数，传入了 {len(args)}")
            self.push_scope(dict(zip(params, args)))
            try:
                self.execute(body)
                result = 0
            except ReturnException as ret:
                result = ret.value
            finally:
                self.pop_scope()
            return result

        # 导入模块中的函数
        for mod in self.imported_modules.values():
            if hasattr(mod, name) and callable(getattr(mod, name)):
                return getattr(mod, name)(*args)

        raise LangError(f"未定义的函数 '{name}'")

# ==================== 便捷函数 ====================
def run_code(code, interpreter=None):
    """运行 SimpleLang 代码"""
    if interpreter is None:
        interpreter = Interpreter()
    lexer = Lexer(code)
    tokens = lexer.tokenize()
    parser = Parser(tokens)
    ast = parser.parse()
    interpreter.interpret(ast)
    return interpreter

def run_file(path):
    """运行 .sl 文件"""
    with open(path, 'r', encoding='utf-8') as f:
        code = f.read()
    return run_code(code)

# ==================== REPL ====================
BANNER = f"""
SimpleLang {__version__} (Python {sys.version.split()[0]})
输入代码直接执行，.exit 退出，.help 帮助
"""

HELP_TEXT = """
SimpleLang 帮助:

  命令:
    .exit  .quit     退出 REPL
    .help            显示此帮助
    .vars            查看当前变量
    .clear           清屏

  关键字: var if else while for in break continue func return print input import try catch

  内置函数: print input len range type_of to_int to_float to_str to_bool

  标准库:
    HTTP:     http_get(url)  http_post(url, data)
    JSON:     json_parse(text)  json_stringify(obj)
    文件:     file_read(path)  file_write(path, content)  file_append  file_exists  file_delete  file_list_dir  file_mkdir
    正则:     regex_match(pattern, text)  regex_replace  regex_test
    数据库:   db_open(path)  db_execute(conn, sql)  db_query(conn, sql)  db_close(conn)
    加密:     hash_md5  hash_sha256  hash_sha1  base64_encode  base64_decode
    字符串:   str_split  str_join  str_replace  str_contains  str_upper  str_lower  str_trim  str_length  str_substring
    数学:     math_abs  math_ceil  math_floor  math_round  math_sqrt  math_pow  math_sin  math_cos  math_random  math_random_int
    数组:     array_push  array_pop  array_shift  array_unshift  array_length  array_join  array_sort  array_reverse  array_index_of  array_slice
    字典:     dict_keys  dict_values  dict_has  dict_remove
    时间:     time_now  time_format  time_sleep
"""

def repl():
    """交互式 REPL"""
    interpreter = Interpreter()
    buffer = ""
    print(BANNER)

    try:
        while True:
            prompt = "... " if buffer else ">>> "
            try:
                line = input(prompt)
            except (EOFError, KeyboardInterrupt):
                print("\n再见!")
                break

            line = line.rstrip()

            # 空行跳过
            if not line and not buffer:
                continue

            # 命令处理
            if not buffer and line.startswith('.'):
                cmd = line[1:].strip().lower()
                if cmd in ('exit', 'quit'):
                    print("再见!")
                    break
                elif cmd == 'help':
                    print(HELP_TEXT)
                elif cmd == 'vars':
                    for i, scope in enumerate(reversed(interpreter.scopes)):
                        print(f"--- 作用域 {len(interpreter.scopes) - i - 1} ---")
                        for k, v in scope.items():
                            v_str = repr(v)
                            if len(v_str) > 100:
                                v_str = v_str[:100] + "..."
                            print(f"  {k} = {v_str}")
                elif cmd == 'clear':
                    os.system('cls' if os.name == 'nt' else 'clear')
                elif cmd:
                    print(f"未知命令: .{cmd} (输入 .help 查看帮助)")
                continue

            buffer += line + "\n"

            # 检查花括号平衡
            open_braces = buffer.count('{') - buffer.count('}')
            if open_braces > 0:
                continue

            # 执行代码
            buffer_stripped = buffer.strip()
            if buffer_stripped:
                try:
                    lexer = Lexer(buffer_stripped)
                    tokens = lexer.tokenize()
                    parser = Parser(tokens)
                    ast = parser.parse()
                    interpreter.interpret(ast)
                    # 显示最后表达式结果
                    if interpreter._last_result is not None:
                        print(f"= {repr(interpreter._last_result)}")
                except LangError as e:
                    print(f"语法错误: {e}")
                except ReturnException as e:
                    print(f"= {repr(e.value)}")
                except Exception as e:
                    print(f"运行时错误: {e}")

            buffer = ""

    except Exception as e:
        print(f"REPL 错误: {e}")

# ==================== 主入口 ====================
def main():
    args = sys.argv[1:]

    if not args:
        repl()
        return

    if args[0] in ('-v', '--version'):
        print(f"SimpleLang {__version__}")
        return

    if args[0] == '-c' and len(args) > 1:
        code = args[1]
        try:
            run_code(code)
        except LangError as e:
            print(f"语法错误: {e}", file=sys.stderr)
            sys.exit(1)
        except Exception as e:
            print(f"运行时错误: {e}", file=sys.stderr)
            sys.exit(1)
        return

    # 运行文件
    filepath = args[0]
    if not os.path.exists(filepath):
        # 尝试添加 .sl 扩展名
        filepath_sl = filepath + '.sl'
        if os.path.exists(filepath_sl):
            filepath = filepath_sl
        else:
            print(f"错误: 文件 '{filepath}' 不存在", file=sys.stderr)
            sys.exit(1)

    try:
        run_file(filepath)
    except LangError as e:
        print(f"语法错误: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"运行时错误: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()