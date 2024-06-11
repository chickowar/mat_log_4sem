from collections import deque


class Node:
    def __init__(self, value, left=None, right=None):
        self.value = value
        self.left = left
        self.right = right
        self.expression = ''
        self.simple_exp = ''

    # перегрузка операторов
    def __repr__(self):
        return str(self)

    def __str__(self):
        if self.simple_exp:
            return self.simple_exp
        else:
            return self.simple_expression()

    def __eq__(self, other):
        return self.expression == other.expression

    # получаем expression
    def simple_expression(self):
        if self.value == '>':
            if self.right.value != '>':
                self.simple_exp = f"{self.left.simple_expression()}>{self.right.simple_expression()}"
                return self.simple_exp
            else:
                self.simple_exp = f"{self.left.simple_expression()}>({self.right.simple_expression()})"
                return self.simple_exp
        else:
            self.simple_exp = self.value
            return self.value

    def get_expression(self):
        if self.expression:
            return self.expression
        if self.value == '>':
            self.expression = f"({self.left.get_expression()}>{self.right.get_expression()})"
        else:
            self.expression = self.value
        return self.expression

    def copy(self):
        return parse(self.expression)


class Parser:
    def __init__(self, s : str):
        self.d = deque(s.replace(' ', ''))
        self.d.append('') # чтобы парсер знал когда остановиться

    def parse_inside(self):
        if not self.d[0]:
            return None
        left = self.parse_term()
        while True:
            if self.d[0] != '>':
                break
            op = self.d.popleft()
            right = self.parse_term()
            left = Node(op, left, right) # присоединяем левый терм к правому
        return left

    def parse_term(self):
        if self.d[0].isalpha():
            node = Node(self.d.popleft())
            return node
        elif self.d[0] == '(':
            self.d.popleft()
            node = self.parse_inside() # парсим подскобочное выражение
            if self.d[0] == ')': # на всякий случай избавляемся от закрывающей скобки (хотя такого вроде не должно быть)
                self.d.popleft()
            return node


def parse(s):
    parser = Parser(s.replace(' ', ''))
    if len(s) == 1:
        ast = Node(s)
        ast.simple_expression()
    else:
        ast = parser.parse_inside()
    ast.get_expression()
    ast.simple_expression()
    return ast


def check(s0: str):
    s = s0.replace(' ', '')
    if 0 <= len(s) <= 2:
        if len(s) != 1 or s[0] == '(' or s[0] == ')' or s[0] == '>':
            return False
        return True

    p = 0
    for i in range(0, len(s)):
        p += int(s[i] == '(') - int(s[i] == ')')
        if p < 0:
            return False
    if p != 0:
        return False

    if s[0] == ')' or s[0] == '>':
        return False

    for i in range(1, len(s) - 1):
        if s[i] == '>' and (s[i + 1] == '>' or s[i + 1] == ')'):
            return False
        if s[i] == '(' and (s[i + 1] == ')' or s[i + 1] == '>'):
            return False
        if s[i] == ')' and (s[i + 1] == '(' or (s[i + 1] != '>' and s[i + 1] != ')')):
            return False
        if (s[i] != '>' and s[i] != ')' and s[i] != '(') and (
                (s[i + 1] != '>' and s[i + 1] != ')' and s[i + 1] != '(') or (s[i + 1] == '(')):
            return False
    if s[-1] == '>':
        return False
    return True


debug = False
if debug:
    # a = Node('s')
    # if a.left:
    #     print(1)
    # Проверка
    print("!!!!!------my_parser-------!!!!!")
    expression = "(p>p)>p>((p>p)>(p>p))"
    parser = Parser(expression)
    syntax_tree = parser.parse_inside()
    print(syntax_tree.simple_expression())
    print("Слева", syntax_tree.left)
    print("Справа", syntax_tree.right)