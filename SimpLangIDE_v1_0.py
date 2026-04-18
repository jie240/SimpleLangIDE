
import sys
import os
import re
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, scrolledtext
import traceback
import tempfile
import subprocess
import shutil


class LangError(Exception):
    def __init__(self, msg, line, col):
        super().__init__(f"[行 {line}, 列 {col}] {msg}")


class Token:
    def __init__(self, type_, value, line, col):
        self.type = type_
        self.value = value
        self.line = line
        self.col = col


class Lexer:
    def __init__(self, code):
        self.code = code
        self.pos = 0
        self.line = 1
        self.col = 1
        self.tokens = []

    def tokenize(self):
        while self.pos < len(self.code):
            ch = self.code[self.pos]
            if ch in ' \t':
                self.advance()
                continue
            if ch == '\n':
                self.line += 1
                self.col = 1
                self.advance()
                continue
            if ch == '/' and self.peek() == '/':
                self.advance(2)
                while self.pos < len(self.code) and self.code[self.pos] != '\n':
                    self.advance()
                continue
            if ch == '/' and self.peek() == '*':
                self.advance(2)
                while self.pos < len(self.code) and not (self.code[self.pos] == '*' and self.peek() == '/'):
                    if self.code[self.pos] == '\n':
                        self.line += 1
                        self.col = 1
                    self.advance()
                self.advance(2)
                continue
            if ch.isdigit():
                num = ''
                while self.pos < len(self.code) and self.code[self.pos].isdigit():
                    num += self.code[self.pos]
                    self.advance()
                self.tokens.append(Token('NUMBER', int(num), self.line, self.col))
                continue
            if ch.isalpha() or ch == '_':
                ident = ''
                while self.pos < len(self.code) and (self.code[self.pos].isalnum() or self.code[self.pos] == '_'):
                    ident += self.code[self.pos]
                    self.advance()
                keywords = {
                    'var': 'VAR', 'if': 'IF', 'else': 'ELSE', 'while': 'WHILE',
                    'func': 'FUNC', 'return': 'RETURN', 'print': 'PRINT',
                    'input': 'INPUT', 'input_str': 'INPUT_STR'
                }
                token_type = keywords.get(ident, 'IDENTIFIER')
                self.tokens.append(Token(token_type, ident, self.line, self.col))
                continue
            if ch == '"':
                self.advance()
                string = ''
                while self.pos < len(self.code) and self.code[self.pos] != '"':
                    if self.code[self.pos] == '\\' and self.peek() == '"':
                        string += '"'
                        self.advance(2)
                        continue
                    if self.code[self.pos] == '\\' and self.peek() == 'n':
                        string += '\n'
                        self.advance(2)
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
            two_char = {'==': 'EQ', '!=': 'NE', '<=': 'LE', '>=': 'GE', '&&': 'AND', '||': 'OR'}
            if self.pos+1 < len(self.code) and ch + self.peek() in two_char:
                op = ch + self.peek()
                self.tokens.append(Token(two_char[op], op, self.line, self.col))
                self.advance(2)
                continue
            single = {
                '+': 'PLUS', '-': 'MINUS', '*': 'MUL', '/': 'DIV', '%': 'MOD',
                '=': 'ASSIGN', '!': 'NOT', '<': 'LT', '>': 'GT',
                '(': 'LPAREN', ')': 'RPAREN', '[': 'LBRACKET', ']': 'RBRACKET',
                '{': 'LBRACE', '}': 'RBRACE', ';': 'SEMICOLON', ',': 'COMMA'
            }
            if ch in single:
                self.tokens.append(Token(single[ch], ch, self.line, self.col))
                self.advance()
                continue
            raise LangError(f"非法字符 '{ch}'", self.line, self.col)
        self.tokens.append(Token('EOF', '', self.line, self.col))
        return self.tokens

    def peek(self):
        return self.code[self.pos+1] if self.pos+1 < len(self.code) else None

    def advance(self, steps=1):
        for _ in range(steps):
            self.pos += 1
            self.col += 1


class ASTNode: pass
class Program(ASTNode):
    def __init__(self, statements): self.statements = statements
class VarDecl(ASTNode):
    def __init__(self, name, init_expr, is_array=False, size_expr=None):
        self.name = name; self.init_expr = init_expr; self.is_array = is_array; self.size_expr = size_expr
class Assign(ASTNode):
    def __init__(self, target, expr): self.target = target; self.expr = expr
class ArrayAccess(ASTNode):
    def __init__(self, name, index_expr): self.name = name; self.index_expr = index_expr
class IfStmt(ASTNode):
    def __init__(self, cond, then_body, else_body): self.cond = cond; self.then_body = then_body; self.else_body = else_body
class WhileStmt(ASTNode):
    def __init__(self, cond, body): self.cond = cond; self.body = body
class ReturnStmt(ASTNode):
    def __init__(self, expr): self.expr = expr
class FuncDef(ASTNode):
    def __init__(self, name, params, body): self.name = name; self.params = params; self.body = body
class FuncCall(ASTNode):
    def __init__(self, name, args): self.name = name; self.args = args
class PrintStmt(ASTNode):
    def __init__(self, exprs): self.exprs = exprs
class InputStmt(ASTNode):
    def __init__(self, var_name, as_str=False): self.var_name = var_name; self.as_str = as_str
class Block(ASTNode):
    def __init__(self, statements): self.statements = statements
class BinaryOp(ASTNode):
    def __init__(self, left, op, right): self.left = left; self.op = op; self.right = right
class UnaryOp(ASTNode):
    def __init__(self, op, expr): self.op = op; self.expr = expr
class Variable(ASTNode):
    def __init__(self, name): self.name = name
class Number(ASTNode):
    def __init__(self, value): self.value = value
class StringLiteral(ASTNode):
    def __init__(self, value): self.value = value


class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def current(self): return self.tokens[self.pos]
    def eat(self, type_):
        tok = self.current()
        if tok.type == type_:
            self.pos += 1
            return tok
        raise LangError(f"期待 {type_}, 实际得到 {tok.type} ('{tok.value}')", tok.line, tok.col)

    def parse(self):
        stmts = []
        while self.current().type != 'EOF':
            stmts.append(self.parse_statement())
        return Program(stmts)

    def parse_statement(self):
        tok = self.current()
        if tok.type == 'VAR': return self.parse_var_decl()
        if tok.type == 'IF': return self.parse_if()
        if tok.type == 'WHILE': return self.parse_while()
        if tok.type == 'FUNC': return self.parse_func_def()
        if tok.type == 'RETURN': return self.parse_return()
        if tok.type == 'PRINT': return self.parse_print()
        if tok.type == 'INPUT' or tok.type == 'INPUT_STR':
            as_str = (tok.type == 'INPUT_STR')
            self.eat(tok.type)
            name = self.eat('IDENTIFIER').value
            self.eat('SEMICOLON')
            return InputStmt(name, as_str)
        if tok.type == 'LBRACE': return self.parse_block()
        if tok.type == 'IDENTIFIER':
            name = self.eat('IDENTIFIER').value
            if self.current().type == 'LBRACKET':
                self.eat('LBRACKET')
                idx = self.parse_expression()
                self.eat('RBRACKET')
                target = ArrayAccess(name, idx)
                if self.current().type == 'ASSIGN':
                    self.eat('ASSIGN')
                    expr = self.parse_expression()
                    self.eat('SEMICOLON')
                    return Assign(target, expr)
                else:
                    self.eat('SEMICOLON')
                    return target
            else:
                if self.current().type == 'ASSIGN':
                    self.eat('ASSIGN')
                    expr = self.parse_expression()
                    self.eat('SEMICOLON')
                    return Assign(Variable(name), expr)
                elif self.current().type == 'LPAREN':
                    args = []
                    self.eat('LPAREN')
                    if self.current().type != 'RPAREN':
                        args.append(self.parse_expression())
                        while self.current().type == 'COMMA':
                            self.eat('COMMA')
                            args.append(self.parse_expression())
                    self.eat('RPAREN')
                    self.eat('SEMICOLON')
                    return FuncCall(name, args)
                else:
                    raise LangError("无效的语句", tok.line, tok.col)
        raise LangError(f"无效的语句开始: {tok.type}", tok.line, tok.col)

    def parse_var_decl(self):
        self.eat('VAR')
        name = self.eat('IDENTIFIER').value
        is_array = False
        size_expr = None
        if self.current().type == 'LBRACKET':
            is_array = True
            self.eat('LBRACKET')
            size_expr = self.parse_expression()
            self.eat('RBRACKET')
        init_expr = None
        if self.current().type == 'ASSIGN':
            self.eat('ASSIGN')
            init_expr = self.parse_expression()
        self.eat('SEMICOLON')
        return VarDecl(name, init_expr, is_array, size_expr)

    def parse_if(self):
        self.eat('IF'); self.eat('LPAREN')
        cond = self.parse_expression()
        self.eat('RPAREN')
        then_body = self.parse_statement()
        else_body = None
        if self.current().type == 'ELSE':
            self.eat('ELSE')
            else_body = self.parse_statement()
        return IfStmt(cond, then_body, else_body)

    def parse_while(self):
        self.eat('WHILE'); self.eat('LPAREN')
        cond = self.parse_expression()
        self.eat('RPAREN')
        body = self.parse_statement()
        return WhileStmt(cond, body)

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
        expr = self.parse_expression() if self.current().type != 'SEMICOLON' else None
        self.eat('SEMICOLON')
        return ReturnStmt(expr)

    def parse_print(self):
        self.eat('PRINT')
        exprs = []
        exprs.append(self.parse_expression())
        while self.current().type == 'COMMA':
            self.eat('COMMA')
            exprs.append(self.parse_expression())
        self.eat('SEMICOLON')
        return PrintStmt(exprs)

    def parse_block(self):
        self.eat('LBRACE')
        stmts = []
        while self.current().type != 'RBRACE':
            stmts.append(self.parse_statement())
        self.eat('RBRACE')
        return Block(stmts)

    def parse_expression(self): return self.parse_logical_or()
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
        if self.current().type in ('NOT', 'MINUS'):
            op = self.eat(self.current().type).value
            expr = self.parse_unary()
            return UnaryOp(op, expr)
        return self.parse_primary()
    def parse_primary(self):
        tok = self.current()
        if tok.type == 'NUMBER':
            self.eat('NUMBER')
            return Number(tok.value)
        elif tok.type == 'STRING':
            self.eat('STRING')
            return StringLiteral(tok.value)
        elif tok.type == 'IDENTIFIER':
            name = self.eat('IDENTIFIER').value
            if self.current().type == 'LBRACKET':
                self.eat('LBRACKET')
                idx = self.parse_expression()
                self.eat('RBRACKET')
                return ArrayAccess(name, idx)
            elif self.current().type == 'LPAREN':
                args = []
                self.eat('LPAREN')
                if self.current().type != 'RPAREN':
                    args.append(self.parse_expression())
                    while self.current().type == 'COMMA':
                        self.eat('COMMA')
                        args.append(self.parse_expression())
                self.eat('RPAREN')
                return FuncCall(name, args)
            else:
                return Variable(name)
        elif tok.type == 'LPAREN':
            self.eat('LPAREN')
            expr = self.parse_expression()
            self.eat('RPAREN')
            return expr
        else:
            raise LangError(f"意外的符号 {tok.type}", tok.line, tok.col)


class ReturnException(Exception):
    def __init__(self, value): self.value = value

class Interpreter:
    def __init__(self, output_callback=None, input_callback=None):
        self.scopes = [{}]
        self.functions = {}
        self.output_callback = output_callback or (lambda x: print(x, end=''))
        self.input_callback = input_callback or (lambda prompt: input(prompt))

    def push_scope(self, vars_dict=None):
        self.scopes.append(vars_dict if vars_dict else {})

    def pop_scope(self):
        if len(self.scopes) > 1:
            self.scopes.pop()

    def get_var(self, name):
        for scope in reversed(self.scopes):
            if name in scope:
                return scope[name]
        raise LangError(f"未定义的变量 '{name}'", 0, 0)

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
        if isinstance(stmt, VarDecl):
            val = 0
            if stmt.init_expr:
                val = self.evaluate(stmt.init_expr)
            if stmt.is_array:
                size = self.evaluate(stmt.size_expr) if stmt.size_expr else 0
                arr = [0] * int(size)
                self.set_var(stmt.name, arr)
            else:
                self.set_var(stmt.name, val)
        elif isinstance(stmt, Assign):
            val = self.evaluate(stmt.expr)
            if isinstance(stmt.target, Variable):
                self.set_var(stmt.target.name, val)
            elif isinstance(stmt.target, ArrayAccess):
                arr = self.get_var(stmt.target.name)
                idx = int(self.evaluate(stmt.target.index_expr))
                arr[idx] = val
        elif isinstance(stmt, IfStmt):
            if self.evaluate(stmt.cond):
                self.execute(stmt.then_body)
            elif stmt.else_body:
                self.execute(stmt.else_body)
        elif isinstance(stmt, WhileStmt):
            while self.evaluate(stmt.cond):
                self.execute(stmt.body)
        elif isinstance(stmt, FuncDef):
            self.functions[stmt.name] = (stmt.params, stmt.body)
        elif isinstance(stmt, ReturnStmt):
            val = self.evaluate(stmt.expr) if stmt.expr else 0
            raise ReturnException(val)
        elif isinstance(stmt, PrintStmt):
            parts = []
            for e in stmt.exprs:
                parts.append(str(self.evaluate(e)))
            self.output_callback(''.join(parts) + '\n')
        elif isinstance(stmt, InputStmt):
            prompt = "请输入字符串: " if stmt.as_str else "请输入数字: "
            val = self.input_callback(prompt)
            if not stmt.as_str:
                try:
                    val = float(val) if '.' in val else int(val)
                except:
                    val = 0
            self.set_var(stmt.var_name, val)
        elif isinstance(stmt, FuncCall):
            self.evaluate(stmt)
        elif isinstance(stmt, Block):
            for s in stmt.statements:
                self.execute(s)

    def evaluate(self, expr):
        if isinstance(expr, Number):
            return expr.value
        if isinstance(expr, StringLiteral):
            return expr.value
        if isinstance(expr, Variable):
            return self.get_var(expr.name)
        if isinstance(expr, ArrayAccess):
            arr = self.get_var(expr.name)
            idx = int(self.evaluate(expr.index_expr))
            return arr[idx]
        if isinstance(expr, BinaryOp):
            left = self.evaluate(expr.left)
            right = self.evaluate(expr.right)
            op = expr.op
            if op == '+': return left + right
            if op == '-': return left - right
            if op == '*': return left * right
            if op == '/':
                if right == 0: raise LangError("除零错误", 0, 0)
                return left / right
            if op == '%':
                if right == 0: raise LangError("模零错误", 0, 0)
                return left % right
            if op == '==': return left == right
            if op == '!=': return left != right
            if op == '<': return left < right
            if op == '>': return left > right
            if op == '<=': return left <= right
            if op == '>=': return left >= right
            if op == '&&': return left and right
            if op == '||': return left or right
        if isinstance(expr, UnaryOp):
            val = self.evaluate(expr.expr)
            if expr.op == '!': return not val
            if expr.op == '-': return -val
        if isinstance(expr, FuncCall):
            if expr.name == 'len':
                arg = self.evaluate(expr.args[0])
                return len(str(arg))
            if expr.name == 'to_int':
                arg = self.evaluate(expr.args[0])
                return int(float(arg))
            if expr.name == 'to_str':
                arg = self.evaluate(expr.args[0])
                return str(arg)
            if expr.name in self.functions:
                params, body = self.functions[expr.name]
                args = [self.evaluate(a) for a in expr.args]
                self.push_scope(dict(zip(params, args)))
                try:
                    self.execute(body)
                    result = 0
                except ReturnException as ret:
                    result = ret.value
                finally:
                    self.pop_scope()
                return result
            raise LangError(f"未定义的函数 '{expr.name}'", 0, 0)
        return 0


class SimpleLangIDE:
    def __init__(self, root):
        self.root = root
        self.root.title("SimpLang IDE - 一小时速成编程语言")
        self.root.geometry("900x700")
        self.file_path = None

        menubar = tk.Menu(root)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="新建", command=self.new_file)
        file_menu.add_command(label="打开", command=self.open_file)
        file_menu.add_command(label="保存", command=self.save_file)
        file_menu.add_command(label="另存为", command=self.save_as_file)
        file_menu.add_separator()
        file_menu.add_command(label="退出", command=root.quit)
        menubar.add_cascade(label="文件", menu=file_menu)

        run_menu = tk.Menu(menubar, tearoff=0)
        run_menu.add_command(label="运行 (F5)", command=self.run_code)
        run_menu.add_command(label="打包为 EXE...", command=self.build_exe)
        menubar.add_cascade(label="运行", menu=run_menu)

        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="关于", command=self.show_about)
        menubar.add_cascade(label="帮助", menu=help_menu)
        root.config(menu=menubar)

        main_paned = tk.PanedWindow(root, orient=tk.VERTICAL, sashrelief=tk.RAISED, sashwidth=5)
        main_paned.pack(fill=tk.BOTH, expand=True)

        editor_frame = tk.Frame(main_paned)
        main_paned.add(editor_frame, height=500)

        self.line_numbers = tk.Text(editor_frame, width=4, padx=3, takefocus=0, border=0,
                                    background='lightgrey', state='disabled', wrap='none')
        self.line_numbers.pack(side=tk.LEFT, fill=tk.Y)

        self.editor = scrolledtext.ScrolledText(editor_frame, wrap=tk.NONE, undo=True)
        self.editor.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        self.editor.bind('<KeyRelease>', self.on_key_release)
        self.editor.bind('<F5>', lambda e: self.run_code())
        self.editor.bind('<Control-s>', lambda e: self.save_file())
        self.editor.bind('<Control-o>', lambda e: self.open_file())
        self.editor.bind('<Control-n>', lambda e: self.new_file())

        output_frame = tk.Frame(main_paned)
        main_paned.add(output_frame, height=200)
        tk.Label(output_frame, text="输出:", anchor='w').pack(fill=tk.X)
        self.output_text = scrolledtext.ScrolledText(output_frame, height=8, wrap=tk.WORD, state='normal')
        self.output_text.pack(fill=tk.BOTH, expand=True)

        self.status_bar = tk.Label(root, text="就绪", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        self.setup_tags()
        self.new_file()
        self.update_line_numbers()
        self.editor.focus_set()

    def setup_tags(self):
        self.editor.tag_configure("keyword", foreground="blue")
        self.editor.tag_configure("string", foreground="green")
        self.editor.tag_configure("comment", foreground="gray")
        self.editor.tag_configure("number", foreground="purple")

    def highlight_syntax(self, event=None):
        code = self.editor.get("1.0", tk.END)
        for tag in ["keyword", "string", "comment", "number"]:
            self.editor.tag_remove(tag, "1.0", tk.END)
        keywords = r'\b(var|if|else|while|func|return|print|input|input_str)\b'
        for match in re.finditer(keywords, code):
            start = f"1.0+{match.start()}c"
            end = f"1.0+{match.end()}c"
            self.editor.tag_add("keyword", start, end)
        for match in re.finditer(r'"[^"\\]*(\\.[^"\\]*)*"', code):
            start = f"1.0+{match.start()}c"
            end = f"1.0+{match.end()}c"
            self.editor.tag_add("string", start, end)
        for match in re.finditer(r'//.*$', code, re.MULTILINE):
            start = f"1.0+{match.start()}c"
            end = f"1.0+{match.end()}c"
            self.editor.tag_add("comment", start, end)
        for match in re.finditer(r'\b\d+\b', code):
            start = f"1.0+{match.start()}c"
            end = f"1.0+{match.end()}c"
            self.editor.tag_add("number", start, end)

    def update_line_numbers(self, event=None):
        lines = self.editor.get("1.0", tk.END).count("\n")
        line_numbers_str = "\n".join(str(i) for i in range(1, lines+1))
        self.line_numbers.config(state='normal')
        self.line_numbers.delete("1.0", tk.END)
        self.line_numbers.insert("1.0", line_numbers_str)
        self.line_numbers.config(state='disabled')

    def on_key_release(self, event=None):
        self.update_line_numbers()
        self.highlight_syntax()
        pos = self.editor.index(tk.INSERT)
        line, col = pos.split('.')
        self.status_bar.config(text=f"行: {line}  列: {col}")

    def new_file(self):
        self.editor.delete("1.0", tk.END)
        self.file_path = None
        self.root.title("SimpLang IDE - 新文件")
        self.update_line_numbers()

    def open_file(self):
        path = filedialog.askopenfilename(filetypes=[("SimpLang 文件", "*.sl"), ("所有文件", "*.*")])
        if path:
            with open(path, 'r', encoding='utf-8') as f:
                code = f.read()
            self.editor.delete("1.0", tk.END)
            self.editor.insert("1.0", code)
            self.file_path = path
            self.root.title(f"SimpLang IDE - {os.path.basename(path)}")
            self.update_line_numbers()
            self.highlight_syntax()

    def save_file(self):
        if self.file_path:
            with open(self.file_path, 'w', encoding='utf-8') as f:
                f.write(self.editor.get("1.0", tk.END))
            self.status_bar.config(text="已保存")
        else:
            self.save_as_file()

    def save_as_file(self):
        path = filedialog.asksaveasfilename(defaultextension=".sl", filetypes=[("SimpLang 文件", "*.sl")])
        if path:
            self.file_path = path
            self.save_file()
            self.root.title(f"SimpLang IDE - {os.path.basename(path)}")

    def run_code(self):
        code = self.editor.get("1.0", tk.END)
        self.output_text.delete("1.0", tk.END)
        try:
            lexer = Lexer(code)
            tokens = lexer.tokenize()
            parser = Parser(tokens)
            ast = parser.parse()

            def output_callback(s):
                self.output_text.insert(tk.END, s)
                self.output_text.see(tk.END)
                self.root.update()

            def input_callback(prompt):
                return simpledialog.askstring("输入", prompt, parent=self.root) or ""

            interpreter = Interpreter(output_callback, input_callback)
            interpreter.interpret(ast)
            self.status_bar.config(text="运行完成")
        except LangError as e:
            output_callback(f"语法错误: {e}\n")
            self.status_bar.config(text="运行出错")
        except Exception as e:
            output_callback(f"运行时错误: {traceback.format_exc()}\n")
            self.status_bar.config(text="运行出错")

    def show_about(self):
        messagebox.showinfo("关于", "SimpLang IDE\n简易 C 风格语言解释器\n内置一键打包 EXE 功能\n版本 1.0")

    def build_exe(self):
        try:
            import PyInstaller
        except ImportError:
            messagebox.showerror("错误", "未找到 PyInstaller。\n请在命令行执行: pip install pyinstaller")
            return

        code = self.editor.get("1.0", tk.END).strip()
        if not code:
            messagebox.showwarning("警告", "代码为空，无法打包。")
            return

        out_dir = filedialog.askdirectory(title="选择 EXE 输出目录")
        if not out_dir:
            return

        exe_name = simpledialog.askstring("EXE 名称", "请输入生成的 EXE 文件名（不含扩展名）:", initialvalue="myprogram")
        if not exe_name:
            return

        self.status_bar.config(text="正在生成启动器...")
        self.root.update()

        try:
            with open(__file__, 'r', encoding='utf-8') as f:
                template_code = f.read()
        except:
            messagebox.showerror("错误", "无法读取自身脚本文件，打包失败。")
            return

        placeholder = "# USER_CODE_PLACEHOLDER"
        if placeholder in template_code:
            user_code_escaped = repr(code)
            template_code = template_code.replace(placeholder, f"USER_CODE = {user_code_escaped}")
        else:
            user_code_escaped = repr(code)
            template_code += f"\nUSER_CODE = {user_code_escaped}\n"

        new_main = '''
if __name__ == "__main__":
    lexer = Lexer(USER_CODE)
    tokens = lexer.tokenize()
    parser = Parser(tokens)
    ast = parser.parse()
    interpreter = Interpreter()
    try:
        interpreter.interpret(ast)
    except Exception as e:
        print(f"运行时错误: {e}")
        input("按回车键退出...")
'''
        pattern = r'if __name__ == [\'"]__main__[\'"]:.*?(?=\n# END OF SCRIPT|\Z)'
        template_code = re.sub(pattern, new_main, template_code, flags=re.DOTALL)

        temp_dir = tempfile.gettempdir()
        launcher_path = os.path.join(temp_dir, f"__simplang_launcher_{exe_name}.py")
        with open(launcher_path, 'w', encoding='utf-8') as f:
            f.write(template_code)

        self.status_bar.config(text="正在打包 EXE (可能需要几十秒)...")
        self.root.update()

        cmd = [
            sys.executable, '-m', 'PyInstaller',
            '--onefile',
            '--windowed',
            '--name', exe_name,
            '--distpath', out_dir,
            '--workpath', os.path.join(temp_dir, f'build_{exe_name}'),
            '--specpath', temp_dir,
            launcher_path
        ]

        try:
            result = subprocess.run(cmd, check=True, capture_output=True, text=True)
            os.remove(launcher_path)
            spec_file = os.path.join(temp_dir, f'{exe_name}.spec')
            if os.path.exists(spec_file):
                os.remove(spec_file)
            build_dir = os.path.join(temp_dir, f'build_{exe_name}')
            if os.path.exists(build_dir):
                shutil.rmtree(build_dir, ignore_errors=True)

            exe_full_path = os.path.join(out_dir, f"{exe_name}.exe")
            messagebox.showinfo("打包成功", f"EXE 已生成到:\n{exe_full_path}")
            self.status_bar.config(text="打包完成")
        except subprocess.CalledProcessError as e:
            error_msg = e.stderr if e.stderr else "未知错误"
            messagebox.showerror("打包失败", f"PyInstaller 错误:\n{error_msg}")
            self.status_bar.config(text="打包失败")
        except Exception as e:
            messagebox.showerror("错误", str(e))
            self.status_bar.config(text="打包出错")


def main():
    if 'USER_CODE' in dir():
        lexer = Lexer(USER_CODE)
        tokens = lexer.tokenize()
        parser = Parser(tokens)
        ast = parser.parse()
        interpreter = Interpreter()
        interpreter.interpret(ast)
        input("\n程序执行完毕，按回车键退出...")
    else:
        root = tk.Tk()
        app = SimpleLangIDE(root)
        root.mainloop()


if __name__ == '__main__':
    main()