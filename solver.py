#!/usr/bin/python3

from helpers import longest_path, printAxioms, printLAxioms
from ltl import Sequent, simplify_LTL
from parser import (
    printSTree,
    branches_int,
    run_solve,
    solved,
    l_path,
    get_rules,
    get_loops,
    printAx,
    printLAx,
    total_seq_comp_for_loops,
    seq_len,
    max_loop,
)
from timeit import timeit
import os
import sys


def run(s, prog=False):
    run_solve(s, prog)


def snik(n, i, k):
    ret = f'{"X "*i}p & G({"X "*(i-1)}p => {"X "*i}p)'
    for j in range(n):
        ret += f'& G({"X "*i}p=>{"X "*j}q)'
    ret += f' => {"G "*k}q'
    return ret


if __name__ == "__main__":
    os.system("clear")
    f_strings = []
    print_tree = False
    verbose = False
    if "-t" in sys.argv:
        print_tree = True
        sys.argv.remove("-t")
    if "-v" in sys.argv:
        verbose = True
        sys.argv.remove("-v")
    if "help" in sys.argv:
        print("./solver formula|sequent [-v|-t] [help] \n")
        print("formula - formula in PLTL form")
        print("sequent - sequent in PLTL form")
        print("Atoms are lowercase letters a-z")
        print("Accepted binary operators: ->, V, &")
        print("Accepted unary (and modal) operators: ~, G, X")
        print("Special keyword: T - Tautology. T = (p|~p)")
        print('Example PLTL formula: "(a->(b&T)) & ~(cVd) | G(e&f) -> X a"\n')
        print(
            "Sequent form: f1, ..., fn => g1, ..., gm, where fi and gi are PLTL formulas"
        )
        print(
            "-v - verbose mode - print number of branches, longest path and time to prove"
        )
        print("-t - print proof tree")
        print("help - display this text")
        print()
        exit()

    T = "(true)"
    if len(sys.argv) == 1:
        f_strings = ["(a->(b&T)) & ~(cVd) | G(e&f) -> X a"]
    else:
        f_strings = [sys.argv[1]]
    for index, f_s in enumerate(f_strings):
        sequent_size = seq_len(f_strings[index], False)
        a_f = []
        d_f = []
        f_s = f_s.replace("T", "(True)").replace("V", "|")
        if "=>" in f_s:
            af = f_s.split("=>")[0].split(",")
            if len(af) == 1:
                a = str(af[0])
                if a.replace(" ", "") == "":
                    del af[0]

            df = f_s.split("=>")[1].split(",")
            if len(df) == 1:
                d = str(df[0])
                if d.replace(" ", "") == "":
                    del df[0]
            for a in af:
                a_f.append(simplify_LTL(a))
            for d in df:
                d_f.append(simplify_LTL(d))
        else:
            d_f.append(simplify_LTL(f_s))

        s = Sequent(ansc=a_f, desc=d_f)
        print(f"Input sequent: {f_strings[index]}")
        if verbose:
            print(f"Input sequent length: {sequent_size}")

        time = 0
        number = 1
        s = Sequent(ansc=a_f, desc=d_f)
        time = timeit("run(s, True)", globals=locals(), number=number)
        time = time / number

        print()
        print(solved())
        if verbose:
            print(f"Branches: {branches_int()}, Longest path: {l_path()}, Time: {time}")
            print(f"Rules used: {get_rules()}")
            # printAx()
            # printLAx()
            print(f"Number of comparisons done: {total_seq_comp_for_loops()}")
            print(f"Longest loop {max_loop()}")
            print(f"Number of loops: {len(get_loops())}")
        else:
            print(f"Time: {time}")
        if print_tree:
            printSTree()
            print()
        print()
