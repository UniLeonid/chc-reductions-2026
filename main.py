"""
Сведение задач верификации к дизъюнктам Хорна с ограничениями (CHC).

К каждой задаче нужно написать две функции.

task_N_chc() — система CHC: правила, точно описывающие программу, и запрос со свойством.

task_N_check(model, <вход>, <выход>) — допускает ли модель вашей системы такое
  исполнение функции. Grader решает систему, получает модель (найденные
  инварианты) и вызывает check на конкретных данных. Внутри check:
    1. переведите конкретные данные в термы Z3;
    2. примените к ним свой предикат и подставьте модель: model.eval(P(...));
    3. верните evaluate(...) — упрощение до True / False (None, если не константа).
  Вызывать в check решатель и саму функцию нельзя.

Задача засчитывается, если
  * система выполнима (sat), то есть свойство доказано;
  * реальные исполнения функции модель допускает (check возвращает True);
  * исполнения, нарушающие свойство, модель отвергает (check возвращает False).
В задаче 4 check устроен иначе: по входу (a, b) он возвращает значение
слабейшего предусловия, и оно должно совпасть с реальным поведением функции.

Проверка: python grader.py
"""
from typing import List, Optional

from z3 import *

set_param(proof=True)

def solve_horn(chc, timeout_ms: int = 10_000):
    s = SolverFor("HORN")
    s.set("engine", "spacer")
    s.set("timeout", timeout_ms)
    s.set("xform.inline_eager", False)
    s.set("xform.inline_linear", False)
    s.set("xform.slice", False)
    s.add(chc)
    res = s.check()
    answer = s.model() if res == sat else s.proof() if res == unsat else None
    return res, answer


def evaluate(expr) -> Optional[bool]:
    value = simplify(expr)
    if is_true(value):
        return True
    if is_false(value):
        return False
    return None


##################################################
# Пример: доказать, что n <= 100 => mc91(n) = 91

def mc91(n: int) -> int:
    if n > 100:
        return n - 10
    else:
        return mc91(mc91(n + 11))


Mc91 = Function("Mc91", IntSort(), IntSort(), BoolSort())


def example_chc():
    n, tmp, res = Ints("n tmp res")
    return [
        ForAll([n], Implies(n > 100, Mc91(n, n - 10))),
        ForAll([n, tmp, res], Implies(And(n <= 100, Mc91(n + 11, tmp), Mc91(tmp, res)), Mc91(n, res))),
        ForAll([n, res], Implies(And(Mc91(n, res), n <= 100, res != 91), False)),
    ]


def example_check(model, n: int, res: int) -> Optional[bool]:
    return evaluate(model.eval(Mc91(IntVal(n), IntVal(res))))


##################################################
# Задача 1 (1 балл). Цикл.
# Доказать: x >= 0  =>  double(x) = 2 * x

def double(x: int) -> int:
    i = 0
    z = 0
    while i < x:
        i = i + 1
        z = z + 2
    return z


Loop1 = Function("Loop1", IntSort(), IntSort(), IntSort(), BoolSort())
Double = Function("Double", IntSort(), IntSort(), BoolSort())

def task_1_chc():
    x, i, z, res = Ints("x i z res")
    return [
        ForAll([x], Loop1(x, 0, 0)),

        ForAll([x, i, z], Implies(
            And(Loop1(x, i, z), i < x),
            Loop1(x, i + 1, z + 2)
        )),

        ForAll([x, i, z], Implies(
            And(Loop1(x, i, z), Not(i < x)),
            Double(x, z)
        )),

        ForAll([x, res], Implies(
            And(Double(x, res), x >= 0, res != 2 * x),
            False
        ))
    ]


def task_1_check(model, x: int, res: int) -> Optional[bool]:
    return evaluate(model.eval(Double(IntVal(x), IntVal(res))))


##################################################
# Задача 2 (2 балла). Нелинейная рекурсия.
# Доказать: m >= 0 and n >= 0  =>  ack(m, n) >= n

def ack(m: int, n: int) -> int:
    if m == 0:
        return n + 1
    elif n == 0:
        return ack(m - 1, 1)
    else:
        return ack(m - 1, ack(m, n - 1))


Ack = Function("Ack", IntSort(), IntSort(), IntSort(), BoolSort())

def task_2_chc():
    m, n, t, res = Ints("m n t res")
    return [
        ForAll([n], Ack(0, n, n + 1)),

        ForAll([m, res], Implies(
            And(m != 0, Ack(m - 1, 1, res)),
            Ack(m, 0, res)
        )),

        ForAll([m, n, t, res], Implies(
            And(m != 0, n != 0, Ack(m, n - 1, t), Ack(m - 1, t, res)),
            Ack(m, n, res)
        )),

        ForAll([m, n, res], Implies(
            And(Ack(m, n, res), m >= 0, n >= 0, res < n),
            False
        ))
    ]


def task_2_check(model, m: int, n: int, res: int) -> Optional[bool]:
    return evaluate(model.eval(Ack(IntVal(m), IntVal(n), IntVal(res))))


##################################################
# Задача 3 (3 балла). Массивы.
# Доказать для res = search_in_array(array, value):
#   res == -1 or (0 <= res < len(array) and array[res] == value)
#
# Подсказка: список можно представить массивом Z3 и длиной.

def search_in_array(array: List[int], value: int) -> int:
    for i in range(0, len(array)):
        if array[i] == value:
            return i
    return -1

IntArr = ArraySort(IntSort(), IntSort())
Loop3 = Function("Loop3", IntArr, IntSort(), IntSort(), IntSort(), BoolSort())
Search = Function("Search", IntArr, IntSort(), IntSort(), IntSort(), BoolSort())

def task_3_chc():
    array = Array("array", IntSort(), IntSort())
    l, v, i, res = Ints("l v i res")
    return [
        ForAll([array, l, v], Loop3(array, l, v, 0)),

        ForAll([array, l, v, i], Implies(
            And(Loop3(array, l, v, i), i < l, Select(array, i) != v),
            Loop3(array, l, v, i + 1)
        )),

        ForAll([array, l, v, i], Implies(
            And(Loop3(array, l, v, i), i < l, Select(array, i) == v),
            Search(array, l, v, i)
        )),

        ForAll([array, l, v, i], Implies(
            And(Loop3(array, l, v, i), Not(i < l)),
            Search(array, l, v, -1)
        )),

        ForAll([array, l, v, res], Implies(
            And(Search(array, l, v, res), Not(Or(
                res == -1,
                And(0 <= res, res < l, Select(array, res) == v)
            ))),
            False
        ))
    ]


def task_3_check(model, array: List[int], value: int, res: int) -> Optional[bool]:
    array_val = K(IntSort(), IntVal(0))

    for index, element in enumerate(array):
        array_val = Store(array_val, IntVal(index), IntVal(element))

    return evaluate(model.eval(Search(array_val, IntVal(len(array)), IntVal(value), IntVal(res))))


##################################################
# Задача 4 (4 балла). Исключения и слабейшее предусловие.
# Найдите слабейшее предусловие, при котором recursive_simple(a, b) НЕ завершается
# исключением. Предусловие должно получиться из модели:
# постройте систему так, чтобы интерпретация одного из предикатов и была им (или его
# отрицанием).
def recursive_simple(a: int, b: int) -> int:
    if a < 0:
        raise Exception("A is not positive")

    if b < 0:
        raise Exception("B is not positive")

    if a < b:
        res = a
    elif a > b:
        res = recursive_simple(a - 1, b)
    else:
        res = recursive_simple(a - 1, b - 2)

    if res < 17:
        raise Exception("Res is not ok")

    return res


Exception1 = Function("Ex", IntSort(), IntSort(), BoolSort())

def task_4_chc():
    a, b = Ints("a b")
    return [
        ForAll([a, b], Implies(a < 0, Exception1(a, b))),

        ForAll([a, b], Implies(b < 0, Exception1(a, b))),

        ForAll([a, b], Implies(
            And(a >= 0, b >= 0, a < b, a < 17),
            Exception1(a, b)
        )),

        ForAll([a, b], Implies(
            And(a >= 0, b >= 0, a > b, Exception1(a - 1, b)),
            Exception1(a, b)
        )),

        ForAll([a, b], Implies(
            And(a >= 0, b >= 0, a == b, Exception1(a - 1, b - 2)),
            Exception1(a, b)
        ))
    ]


def task_4_check(model, a: int, b: int) -> Optional[bool]:
    """Значение слабейшего предусловия на (a, b): True — исключения не будет."""
    return not evaluate(model.eval(Exception1(IntVal(a), IntVal(b))))


##################################################

if __name__ == "__main__":
    status, model = solve_horn(example_chc())
    print(status)
    print(model)
    print(example_check(model, 50, 91))   # True: реальное исполнение
    print(example_check(model, 50, 90))   # False: нарушает свойство
