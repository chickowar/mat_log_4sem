from my_parser import parse, Node, check

axiom_K = parse("p>(q>p)")
axiom_S = parse("(s>(p>q))>((s>p)>(s>q))")
axiom_Enot = parse("p>f>f>p")


class Rule:
    all_rules = []
    name = "noname"
    # Чтобы добавить новое правило, нужно создать class NewRule(Rule) и в полях указать name,
    # а также должен быть метод try_rule принимающий на вход гипотезу и список доказанных теорем
    # и (желательно) функция message

    def try_rule(self, con : Node, theorems : list):
        print(f"В подклассе класса Rule укажите функцию try_rule для проверки по данному правилу ({self})")
        return None

    def message(self, con, res):
        return f"Теорема [{con}] доказывается правилом {self.name}"

    def __repr__(self):
        return self.name


class MP(Rule):
    name = "Modus Ponens"

    def message(self, con: Node, res):
        return f"Теорема [{con.simple_expression()}] выводится по правилу модус поненс из теорем [{res[0]}] и [{res[1]}]"

    def try_rule(self, con: Node, theorems):
        # if |- A>B and |- A, then |-B
        # Если B (con) получили при помощи MP, то ищем A>B (trm.right == con)
        # тогда А (trm.right) должно быть в theorems. Вот и всё
        for trm in theorems:
            if trm.right == con:
                # Пока что проходимся по списку за линию
                for A in theorems:
                    if trm.left == A:
                        return (A, trm)


class Substitution(Rule):
    name = "Substitution"

    def message(self, con, res):
        if res[1] == res[2] or not res[1]:
            return f"Теорема [{con}] уже есть в списке выводимых теорем"
        else:
            return f"Теорема [{con}] выводима из теоремы [{res[0]}] путём подстановки [{res[2]}] вместо [{res[1]}]"

    def compare_with_substitution(self, con, trm, s_from, s_to):
        return con.expression == trm.expression.replace(s_from, s_to)

    def find_difference(self, con: Node, trm: Node):
        # con - conjecture - формула (теорема, которую проверяем), trm - theorem - теорема (которая выводима)
        # начинаем параллельный dfs, возвращаем либо None - если con не сходится по структуре с trm,
        # либо (p, exp) если натыкаемся на потенциальную замену exp (из con) на p (из trm),
        # (None None) если не нашлась замена
        if con.value == '>':
            if trm.value == '>' or trm.value == 'f':
                return None
            elif trm.value == con.value:
                return (None, None)
            else:
                return (trm.value, con.value)
        for to_c, to_t in [(con.left, trm.left), (con.right, trm.right)]:
            if to_c.value != '>':                           # если в con (гипотезе) - переменная
                if to_t.value == '>' or (to_t.value == 'f' and to_c.value != 'f'):
                    # если в trm поддерево или f, а в con переменная - то структуры не совпадают
                    return None
                if to_c.value == to_t.value:
                    # если переменные одинаковые, то продолжим
                    continue
                else:
                    # если разные, то мы получили потенциальную замену
                    return to_t.value, to_c.value
            if to_t.value != '>':                           # если в trm - переменная
                if to_c.value != to_t.value:
                    return to_t.value, to_c.expression
                else:
                    continue
            if to_t.value == to_c.value:            # если и в trm и в сon поддеревья
                ret = self.find_difference(self, to_c, to_t)     # проходимся по поддереву
                if (not ret) or (ret[0]):               # если структура сломалась или замена нашлась
                    return ret                              # возвращаем None или соответствующую замену
                continue                                # иначе продолжаем
        return (None, None)

    def try_rule(self, con: Node, theorems):
        # возвращает теорему из которой выводится con, то что заменяем из теоремы и то на что заменяем
        for trm in theorems:
            # проверяем можно ли получить con какой-то одной заменой из trm
            if con == trm:
                # Мы даже не делали замены... тавтология какая-то
                return (trm, None, None)
            substitution = self.find_difference(self, con, trm)
            if not substitution:
                continue
            sub_from, sub_to = substitution
            if sub_from == 'f':
                return None
            if self.compare_with_substitution(self, con, trm, sub_from, sub_to):
                return (trm, sub_from, sub_to)
        return None


class Verificator:
    axioms = [axiom_S, axiom_K, axiom_Enot]
    conjecture_fail_message = "Формула [{}] не выводится из теорем ни по одному из правил"
    check_fail_message = "Формула [{}] не является ппф"
    rules = {
        Substitution.name : Substitution,
        MP.name : MP
    }

    def __init__(self, to_prove = '', steps = []):
        self.theorems = Verificator.axioms.copy()
        self.to_prove = to_prove
        self.to_prove_ast = None
        if to_prove:
            self.to_prove_ast = parse(to_prove)
        self.steps = steps

    ####################################################################################################################
    def run(self, write = False):
        ret = None
        if write:
            ret = []
        step_counter = 0
        # ВЫВОДИМ АКСИОМЫ
        print("Для доказательства используем аксиомы (будем считать их выводимыми/доказанными): ")
        if write:
            ret.append("Для доказательства используем аксиомы (будем считать их выводимыми/доказанными): ")
        for a in self.theorems:
            print(a.simple_expression())
            if write:
                ret.append(a.simple_expression())

        # ВВОДИМ ЧТО ДОКАЗЫВАЕМ
        if not self.to_prove:
            self.to_prove = input("Что доказываем: ").replace(' ', '')
            while not check(self.to_prove):
                print(self.check_fail_message.format(self.to_prove))
                self.to_prove = input("Введите адекватную формулу того, что доказываем: ").replace(' ', '')
            self.to_prove_ast = parse(self.to_prove)
        if write and check(self.to_prove):
            ret = [f"Что доказываем: {self.to_prove}"]
        elif write:
            return [f"Формула {self.to_prove} записана неверно"]
        # ВЫВОДИМ ШАГИ ПО ПОРЯДКУ
        if self.steps:
            for con in self.steps:
                step_counter += 1
                print(f"{step_counter}----ШАГ {step_counter}----{step_counter}")
                if write:
                    ret.append(f"{step_counter}----ШАГ {step_counter}----{step_counter}")
                if not check(con):
                    print(self.check_fail_message.format(con))
                    if write:
                        ret.append(self.check_fail_message.format(con))
                    continue
                con_ast = parse(con)
                analysis = self.analyze_conjecture(con_ast)
                print(analysis)
                if write:
                    ret.append(analysis)
                if analysis != self.conjecture_fail_message.format(str(con_ast)):
                    self.theorems.append(con_ast)

        # ЕСЛИ ДОКАЗАНО ИЗ ШАГОВ ОСТАНАВЛИВАЕМСЯ
        if self.to_prove_ast in self.theorems:
            print("=====ДОКАЗАНО=====")
            if write:
                ret.append("=====ДОКАЗАНО=====")
            return ret
        if write:
            ret.append("=====НЕ ДОКАЗАНО=====")
            return ret
        cur_step = ''
        # ПОКА НЕ ДОКАЗАНО, ПОЛУЧАЕМ НОВЫЕ ШАГИ
        while cur_step != self.to_prove_ast.expression:
            step_counter += 1
            print(f"{step_counter}----ШАГ {step_counter}----{step_counter}")
            con = input('Введите формулу: ')
            self.steps.append(con)
            if not check(con):
                print(self.check_fail_message.format(con))
                continue
            con_ast = parse(con)

            analysis = self.analyze_conjecture(con_ast)
            print(analysis)
            if analysis != self.conjecture_fail_message.format(str(con_ast)):
                self.theorems.append(con_ast)
                cur_step = con_ast.expression
                continue
            step_counter -= 1
        print("=====ДОКАЗАНО=====")
        return ret
    ####################################################################################################################

    # Добавить аксиому
    def add_axiom(self, axiom_str):
        axiom_str.replace(' ', '')
        if not check(axiom_str):
            print(f"Аксиома {axiom_str} записана неверно")
            return
        axiom = parse(axiom_str)
        for a in Verificator.axioms:
            if a == axiom:
                print(f"Аксиома {axiom_str} уже в списке аксиом")
                return
        Verificator.axioms.append(axiom)
        print(f"Аксиома {axiom_str} добавлена в список аксиом")
        return

    # Удалить аксиомы
    def remove_axiom(self, axiom_str):
        axiom_str.replace(' ', '')
        if not check(axiom_str):
            print(f"Аксиома {axiom_str} записана неверно")
            return
        axiom = parse(axiom_str)
        for i in range(len(Verificator.axioms)):
            a = Verificator.axioms[i]
            if a == axiom:
                Verificator.axioms.pop(i)
                print(f"Аксиома {axiom_str} удалена")
                return
        print(f"Аксиома {axiom_str} не была в списке аксиом")
        return

    # Проверка гипотезы
    def analyze_conjecture(self, con):
        # Возвращает краткий анализ гипотезы
        if con.value == 'f':
            return f"[f] - константа"
        if con in self.theorems:
            return f"Теорема [{con}] уже есть в списке выводимых теорем"
        for name in self.rules:
            a = self.rules[name].try_rule(self.rules[name], con, self.theorems)
            if a:
                return self.rules[name].message(self.rules[name], con, a)
        return self.conjecture_fail_message.format(str(con))


debug = False
if debug:
    verificator = Verificator()
    verificator.run()