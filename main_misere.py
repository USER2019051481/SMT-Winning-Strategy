from domain.parser import PDDLParser
from generator import MisereGenerator
from z3 import simplify
import time
import os

if __name__ == '__main__':
    start = time.time()
    # 1.Sub
    # 1.1 Take-away

    pwd ="pddl/2.Nim/2.2 Monotonic Nim/Monotonic-3-piled-Nim.pddl"

    # domain = PDDLParser("pddl/2.Nim/2.1 Nim/Two-piled-nim.pddl")
    # domain = PDDLParser("pddl/2.Nim/2.2 Monotonic Nim/Monotonic-2-piled-Nim.pddl")
    domain = PDDLParser("pddl/2.Nim/2.2 Monotonic Nim/Monotonic-3-piled-Nim.pddl")
    # domain = PDDLParser("pddl/2.Nim/2.18 Circular Nim/CircularNim(2,1).pddl")
    # domain = PDDLParser("pddl/2.Nim/2.8 l-Slow Nim/Two-piled-1-slow-nim.pddl")

    # domain = PDDLParser("pddl/1.Sub/1.1 Take-away/Take-away-3.pddl")  # N
    # domain = PDDLParser("pddl/1.Sub/1.2 Subtraction/Subtraction-(1,2,6).pddl")  # N

    # domain = PDDLParser("pddl/2.Nim/2.8 l-Slow Nim/Two-piled-1-slow-nim.pddl")    #Y
    # domain = PDDLParser("pddl/4.Wythoff/4.1 Wythoff/Odd-Even-Wythoff-v2-le-0.pddl")
    # domain = PDDLParser("pddl/4.Wythoff/4.1 Wythoff/Odd-Odd-Wythoff-v2-le-0.pddl")
    # domain = PDDLParser("pddl/4.Wythoff/4.1 Wythoff/Wythoff-v2-le-0.pddl")

    #
    # domain = PDDLParser("pddl/4.Wythoff/4.2 l-Wythoffff Game/Even-Even-l(2)-wythoff-v2-le-0.pddl")
    # domain = PDDLParser("pddl/4.Wythoff/4.2 l-Wythoffff Game/l(1)-wythoff-v2-le-0.pddl")
    # domain = PDDLParser("pddl/5.Chomp/5.2  L-shaped Chomp Game/L_shaped_chomp_game.pddl")
    gen = MisereGenerator( pwd,domain)
    formula_template = gen.generate_formula(0,0)
    formula = simplify(formula_template.formula_model1([],[]))
    cost1 = time.time() - start
    print('*' * 50)
    print('N-formula:\n\t %s' % formula)

    strategies = gen.generate_strategy()
    cost2 = time.time() - start
    print('*' * 50)
    print('strategies:\n', strategies)

    if not os.path.exists("./log1"):
        os.mkdir("./log1")
    with open("./log1/%s" % domain.name, "a") as f:
        print("\n*******************Finished*******************")
        print('N-formula:\n\t %s' % formula)
        print('time cost:\n\t %s' % cost1)
        print('strategies:\n\t %s' % strategies)
        print('time cost:\n\t %s' % cost2)

        print('\nmisere rule', file=f)
        print('N-formula:\t %s' % formula, file=f)
        print('time cost:\t %s' % cost1, file=f)
        print('strategies:\t %s' % strategies, file=f)
        print('time cost:\t %s' % cost2, file=f)
