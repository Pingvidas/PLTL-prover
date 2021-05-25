#!/usr/bin/python

from ltlf2dfa.parser.ltlf import LTLfParser
import re
from sympy.logic import simplify_logic
from sympy import Predicate, Q


class Sequent:
    def __init__(
        self,
        ansc=[],
        desc=[],
        parent=None,
        children=[None, None],
        from_rbox=False,
        rbox_root=None,
        from_rule="",
    ):
        self.ansc = ansc
        self.desc = desc
        self.parent = parent
        self.children = children
        self.from_rbox = from_rbox
        self.rbox_root = rbox_root
        self.from_rule = from_rule

    def __repr__(self):
        toprint = ""
        if len(self.ansc) == 0:
            pass
        else:
            for f in range(len(self.ansc)):
                toprint += f"{self.ansc[f]}"
                if f < len(self.ansc) - 1:
                    toprint += ","
        toprint += "=>"
        if len(self.desc) == 0:
            pass
        else:
            for f in range(len(self.desc)):
                toprint += f"{self.desc[f]}"
                if f < len(self.desc) - 1:
                    toprint += ","
        return toprint.replace(" ", "")

    def __str__(self):
        toprint = ""
        if len(self.ansc) == 0:
            pass
        else:
            for f in range(len(self.ansc)):
                toprint += f"{self.ansc[f]}".replace(" ", "")
                if f < len(self.ansc) - 1:
                    toprint += ", "
        toprint += " => "
        if len(self.desc) == 0:
            pass
        else:
            for f in range(len(self.desc)):
                toprint += f"{self.desc[f]}".replace(" ", "")
                if f < len(self.desc) - 1:
                    toprint += ", "

        return toprint.replace("!", "~").replace("|", "V")


def simplify_LTL(form_str):
    parser = LTLfParser()
    Q.G = Predicate("G")
    Q.X = Predicate("X")
    formula = parser(form_str)
    og_formula = str(formula)
    formula = (
        str(formula)
        .replace("!", "~")
        .replace("G", "Q.G")
        .replace("X", "Q.X")
        .replace(" ", "")
    )
    formula_str = (
        str(simplify_logic(str(formula).replace("->", ">>"), form="dnf"))
        .replace("Q.G", "G")
        .replace("Q.X", "X")
        .replace(">>", "->")
    )
    while True:
        loper = ""
        roper = ""
        find = re.search(r"Implies\((.*?),(.*?)\)", formula_str)
        if find:
            loper = find.group(1)
            roper = find.group(2)
            formula_str = formula_str.replace(f"Implies({loper}", f"({loper})")
            formula_str = formula_str.replace(f",{roper})", f"->({roper})")
            formula_str = formula_str.replace(" ", "")
        else:
            break
    return parser(formula_str)
