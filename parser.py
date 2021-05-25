#!/usr/bin/python

from os import close
from sys import base_exec_prefix
from helpers import *
from ltl import *
from functools import reduce

Stree = []
solved = False
top = []
axioms = []
l_axioms = []
visited = []
closed = []
branches = [1]
saturated = []
sat = False
loop_size_counter = []
rules = {
    "LO": 0,
    "RO": 0,
    "LA": 0,
    "RA": 0,
    "LI": 0,
    "RI": 0,
    "LN": 0,
    "RN": 0,
    "LG": 0,
    "RG": 0,
    "X": 0,
}


def l_path():
    return longest_path(closed)


def reset():
    global Stree
    Stree = []
    global top
    top = []
    global axioms
    axioms = []
    global l_axioms
    l_axioms = []
    global visited
    visited = []
    global closed
    closed = []
    global branches
    branches[0] = 1
    global solved
    solved = False
    global loop_size_counter
    loop_size_counter = []
    global rules
    rules = {
        "LO": 0,
        "RO": 0,
        "LA": 0,
        "RA": 0,
        "LI": 0,
        "RI": 0,
        "LN": 0,
        "RN": 0,
        "LG": 0,
        "RG": 0,
        "X": 0,
    }


def setup(s):
    reset()
    global Stree
    global top
    Stree.append(s)
    top.append(s)


def branches_int():
    return branches[0]


form_pat = re.compile(r"^\((.*?)\)$")
binop_pat = re.compile(r"^\((.*?[&|\||-])\)$")
negop_pat = re.compile(r"^\!\((.*?)\)$")
gleop_pat = re.compile(r"^G\((.*?)\)$")
nxtop_pat = re.compile(r"^X\((.*?)\)$")


def seq_len(sequent, is_seq=True):
    count = 0
    if is_seq:
        for a in sequent.ansc:
            count += (
                len(str(a).replace(" ", ""))
                - str(a).count("(")
                - str(a).count(")")
                - str(d).count("true") * 3
            )
            count -= str(a).count("->")
        for d in sequent.desc:
            count += (
                len(str(d).replace(" ", ""))
                - str(d).count("(")
                - str(d).count(")")
                - str(d).count("true") * 3
            )
            count -= str(d).count("->")
    else:
        count += (
            len(sequent.replace(" ", "").replace(",", "").replace("->", ">"))
            - sequent.count("(")
            - sequent.count(")")
            - sequent.count("true") * 3
        )
        if sequent.count("=>") > 0:
            count = (count - 2) - (sequent.count("=>") - 1)
    return count


def run_solve(s, prog):
    setup(s)
    global solved
    global top
    global Stree
    global closed
    global axioms
    global l_axioms
    if prog:
        print(
            f"\rTree nodes: {len(Stree)}, Closed branches: {len(closed)}, Axioms: {len(axioms)}, Loop Axioms: {len(l_axioms)}",
            end="",
        )
    while len(top) > 0:
        prast(top[-1])
        solve(top[-1])
        if prog:
            print(
                f"\rTree nodes: {len(Stree)}, Closed branches: {len(closed)}, Axioms: {len(axioms)}, Loop Axioms: {len(l_axioms)}",
                end="",
            )
    print(
        f"\rTree nodes: {len(Stree)}, Closed branches: {len(closed)}, Axioms: {len(axioms)}, Loop Axioms: {len(l_axioms)}",
        end="",
    )

    if len(set(closed)) == len(set(axioms).union(set(l_axioms))):
        solved = True
        return True
    else:
        solved = False
        return False


def solve(sequent):
    global saturated, sat, top

    if len(top) > 0:
        if close_saturated(sequent):
            del top[-1]
            if len(top) == 0:
                sat = True
            else:
                return

    if len(top) > 0:
        if close_bin(sequent):
            if len(top) == 0:
                sat = True
            else:
                return

    if len(top) > 0:
        if close_neg(sequent):
            if len(top) == 0:
                sat = True
            else:
                return

    if len(top) > 0:
        if close_lglo(sequent):
            if len(top) == 0:
                sat = True
            else:
                return

    if len(top) > 0:
        if close_rglo(sequent):
            if len(top) == 0:
                sat = True
            else:
                return

    if len(top) > 0:
        saturated.append(sequent)
        del top[-1]
        if len(top) == 0:
            sat = True
    if sat:
        ind = 0
        mixed = []
        e = 0
        for s in saturated:
            close_next(s)
        saturated = []
        sat = False
    return


def close_bin(sequent):
    global Stree
    global top
    global visited
    global axioms
    global branches
    global rules
    found = False
    aindex = 0
    binop = False
    for f in sequent.ansc + sequent.desc:
        fstr = str(f).replace(" ", "")
        temp = re.match(form_pat, fstr)
        if temp and check(temp.group(1)) == "Balanced":
            fstr = temp.group(1)
        left = remove_text_inside_brackets(fstr)
        binop = re.search(r"[&|\||-]", left[0])
        if binop:
            break
    if not binop:
        return False
    for a in sequent.ansc:
        formula_str = str(a).replace(" ", "")
        temp = re.match(r"^\((.*?[&|\||-].*?)\)$", formula_str)
        if temp and check(temp.group(1)) == "Balanced":
            formula_str = temp.group(1)
        left = remove_text_inside_brackets(formula_str)
        outer_bin = left[0]
        outer_bin_index = 0

        if "|" in outer_bin:
            outer_bin_index = left[1]
            outer_bin = "|"
            ancopy = sequent.ansc[:]
            del ancopy[aindex]
            l = simplify_LTL(formula_str[:outer_bin_index])
            r = simplify_LTL(formula_str[outer_bin_index + len(outer_bin) :])
            ancopy1 = ancopy[:]
            ancopy1.append(l)
            ancopy2 = ancopy[:]
            ancopy2.append(r)
            lseq = Sequent(ansc=ancopy1[:], desc=sequent.desc[:])
            rseq = Sequent(ansc=ancopy2[:], desc=sequent.desc[:])
            if sequent.rbox_root:
                lseq.rbox_root = sequent.rbox_root
                rseq.rbox_root = sequent.rbox_root
            sequent.children = [lseq, rseq]
            lseq.parent = sequent
            rseq.parent = sequent
            lseq.from_rule = "(V=>)"
            rseq.from_rule = "(V=>)"
            rules["LO"] += 1
            branches[0] += 1
            visited.append(sequent)
            if len(top) > 0:
                del top[-1]
            Stree.append(lseq)
            Stree.append(rseq)
            top.append(lseq)
            top.append(rseq)
            found = True
            break

        elif "&" in outer_bin:
            rules["LA"] += 1
            outer_bin_index = left[2]
            outer_bin = "&"
            ancopy = sequent.ansc[:]
            del ancopy[aindex]
            l = simplify_LTL(formula_str[:outer_bin_index])
            r = simplify_LTL(formula_str[outer_bin_index + len(outer_bin) :])
            ancopy.append(l)
            ancopy.append(r)
            seq = Sequent(ansc=ancopy, desc=sequent.desc[:])
            sequent.children = [None, seq]
            seq.parent = sequent
            if sequent.rbox_root:
                seq.rbox_root = sequent.rbox_root
            seq.from_rule = "(&=>)"
            visited.append(sequent)
            if len(top) > 0:
                del top[-1]
            Stree.append(seq)
            top.append(seq)
            found = True
            break

        elif "-" in outer_bin:
            rules["LI"] += 1
            outer_bin_index = left[3]
            outer_bin = "->"
            l = simplify_LTL(formula_str[:outer_bin_index])
            r = simplify_LTL(formula_str[outer_bin_index + len(outer_bin) :])
            ancopy1 = sequent.ansc[:]
            ancopy2 = sequent.ansc[:]
            del ancopy1[aindex]
            del ancopy2[aindex]
            decopy1 = sequent.desc[:]
            decopy2 = sequent.desc[:]
            decopy1.append(l)
            ancopy2.append(r)
            lseq = Sequent(ansc=ancopy1, desc=decopy1)
            rseq = Sequent(ansc=ancopy2, desc=decopy2)
            if sequent.rbox_root:
                lseq.rbox_root = sequent.rbox_root
                rseq.rbox_root = sequent.rbox_root
            sequent.children = [lseq, rseq]
            lseq.parent = sequent
            rseq.parent = sequent
            lseq.from_rule = "(->=>)"
            rseq.from_rule = "(->=>)"
            branches[0] += 1
            if len(top) > 0:
                del top[-1]
            Stree.append(lseq)
            Stree.append(rseq)
            top.append(lseq)
            top.append(rseq)
            found = True
            break
        aindex += 1

    if not found:
        bindex = 0
        for d in sequent.desc:
            formula_str = str(d).replace(" ", "")
            temp = re.match(r"^\((.*?[&|\||-].*?)\)$", formula_str)
            if temp and check(temp.group(1)) == "Balanced":
                formula_str = temp.group(1)
            left = remove_text_inside_brackets(formula_str)
            outer_bin = left[0]
            outer_bin_index = 0

            if "|" in outer_bin:
                rules["RO"] += 1
                outer_bin_index = left[1]
                outer_bin = "|"
                decopy = sequent.desc[:]
                del decopy[bindex]
                l = simplify_LTL(formula_str[:outer_bin_index])
                r = simplify_LTL(formula_str[outer_bin_index + len(outer_bin) :])
                decopy.append(l)
                decopy.append(r)
                seq = Sequent(ansc=sequent.ansc[:], desc=decopy[:])
                if sequent.rbox_root:
                    seq.rbox_root = sequent.rbox_root
                sequent.children = [None, seq]
                seq.parent = sequent
                seq.from_rule = "(=>V)"
                visited.append(sequent)
                if len(top) > 0:
                    del top[-1]
                Stree.append(seq)
                top.append(seq)
                found = True
                break

            elif "&" in outer_bin:
                rules["RA"] += 1
                outer_bin_index = left[2]
                outer_bin = "&"
                decopy = sequent.desc[:]
                del decopy[bindex]
                l = simplify_LTL(formula_str[:outer_bin_index])
                r = simplify_LTL(formula_str[outer_bin_index + len(outer_bin) :])
                decopy1 = decopy[:]
                decopy1.append(l)
                decopy2 = decopy[:]
                decopy2.append(r)
                lseq = Sequent(ansc=sequent.ansc[:], desc=decopy1[:])
                rseq = Sequent(ansc=sequent.ansc[:], desc=decopy2[:])
                if sequent.rbox_root:
                    lseq.rbox_root = sequent.rbox_root
                    rseq.rbox_root = sequent.rbox_root
                sequent.children = [lseq, rseq]
                lseq.parent = sequent
                rseq.parent = sequent
                lseq.from_rule = "(=>&)"
                rseq.from_rule = "(=>&)"
                branches[0] += 1
                visited.append(sequent)
                if len(top) > 0:
                    del top[-1]
                Stree.append(lseq)
                Stree.append(rseq)
                top.append(lseq)
                top.append(rseq)
                found = True
                break

            elif "-" in outer_bin:
                rules["RI"] += 1
                outer_bin_index = left[3]
                outer_bin = "->"
                decopy = sequent.desc[:]
                del decopy[bindex]
                l = simplify_LTL(formula_str[:outer_bin_index])
                r = simplify_LTL(formula_str[outer_bin_index + len(outer_bin) :])
                decopy.append(r)
                ancopy = sequent.ansc[:]
                ancopy.append(l)
                seq = Sequent(ansc=ancopy[:], desc=decopy[:])
                if sequent.rbox_root:
                    seq.rbox_root = sequent.rbox_root
                sequent.children = [None, seq]
                seq.parent = sequent
                seq.from_rule = "(=>->)"
                visited.append(sequent)
                if len(top) > 0:
                    del top[-1]
                Stree.append(seq)
                top.append(seq)
                found = True
                break
            bindex += 1
    return found


def close_neg(sequent):
    global Stree
    global top
    global visited
    global axioms
    global rules
    found = False
    aindex = 0
    negop = False
    for f in sequent.ansc + sequent.desc:
        fstr = str(f).replace(" ", "")
        temp = re.match(form_pat, fstr)
        if temp and check(temp.group(1)) == "Balanced":
            fstr = temp.group(1)
        left = remove_text_inside_brackets(fstr)
        negop = re.search(r"!", left[0])
        if negop:
            break
    if not negop:
        return False
    for a in sequent.ansc:
        formula_str = str(a).replace(" ", "")
        temp = re.match(r"^\!\((.*?)\)$", formula_str)
        if temp and check(temp.group(1)) == "Balanced":
            formula_str = temp.group(1)
            ancopy = sequent.ansc[:]
            del ancopy[aindex]
            decopy = sequent.desc[:]
            decopy.append(simplify_LTL(formula_str))
            visited.append(sequent)
            seq = Sequent(ansc=ancopy, desc=decopy)
            if sequent.rbox_root:
                seq.rbox_root = sequent.rbox_root
            sequent.children = [None, seq]
            seq.parent = sequent
            seq.from_rule = "(~=>)"
            if len(top) > 0:
                del top[-1]
            Stree.append(seq)
            top.append(seq)
            found = True
            rules["LN"] += 1
            break
        aindex += 1

    dindex = 0
    for d in sequent.desc:
        formula_str = str(d).replace(" ", "")
        temp = re.match(r"^\!\((.*?)\)$", formula_str)
        if temp and check(temp.group(1)) == "Balanced":
            formula_str = temp.group(1)
            ancopy = sequent.ansc[:]
            decopy = sequent.desc[:]
            del decopy[dindex]
            ancopy.append(simplify_LTL(formula_str))
            visited.append(sequent)
            seq = Sequent(ansc=ancopy, desc=decopy)
            if sequent.rbox_root:
                seq.rbox_root = sequent.rbox_root
            sequent.children = [None, seq]
            seq.parent = sequent
            seq.from_rule = "(=>~)"
            if len(top) > 0:
                del top[-1]
            Stree.append(seq)
            top.append(seq)
            found = True
            rules["RN"] += 1
            break
        dindex += 1
    return found


def close_lglo(sequent):
    global Stree
    global top
    global visited
    global axioms
    global rules
    found = False
    gleop = False
    for f in sequent.ansc + sequent.desc:
        fstr = str(f).replace(" ", "")
        temp = re.match(form_pat, fstr)
        if temp and check(temp.group(1)) == "Balanced":
            fstr = temp.group(1)
        left = remove_text_inside_brackets(fstr)
        gleop = f in sequent.ansc and re.match(r"G", left[0])
        if gleop:
            break
    if not gleop:
        return False
    aindex = 0
    for a in sequent.ansc:
        formula_str = str(a).replace(" ", "")
        temp = re.match(r"^G\((.*?)\)$", formula_str)
        if temp and check(temp.group(1)) == "Balanced":
            formula_str = temp.group(1)
            ancopy = sequent.ansc[:]
            del ancopy[aindex]
            decopy = sequent.desc[:]
            visited.append(sequent)
            ancopy.append(formula_str)
            ancopy.append(f"X(G({formula_str}))")
            seq = Sequent(ansc=ancopy, desc=decopy)
            if sequent.rbox_root:
                seq.rbox_root = sequent.rbox_root
            sequent.children = [None, seq]
            seq.parent = sequent
            seq.from_rule = "(G=>)"
            if len(top) > 0:
                del top[-1]
            Stree.append(seq)
            top.append(seq)
            found = True
            rules["LG"] += 1
            break
        aindex += 1
    return found


def close_rglo(sequent):
    global Stree
    global top
    global visited
    global axioms
    global branches
    global rules
    found = False
    dindex = 0
    for d in sequent.desc:
        formula_str = str(d).replace(" ", "")
        temp = re.match(r"^G\((.*?)\)$", formula_str)
        if temp and check(temp.group(1)) == "Balanced":
            formula_str = temp.group(1)
            ancopy = sequent.ansc[:]
            decopy1 = sequent.desc[:]
            decopy2 = sequent.desc[:]
            del decopy1[dindex]
            del decopy2[dindex]
            decopy1.append(simplify_LTL(formula_str))
            decopy2.append(simplify_LTL(f"X(G({formula_str}))"))

            visited.append(sequent)
            lseq = Sequent(ansc=ancopy, desc=decopy1)
            root = sequent
            if sequent.rbox_root:
                root = sequent.rbox_root
            rseq = Sequent(ansc=ancopy, desc=decopy2, from_rbox=True, rbox_root=root)
            sequent.children = [lseq, rseq]
            lseq.parent = sequent
            rseq.parent = sequent
            lseq.from_rule = "(=>G)"
            rseq.from_rule = "(=>G)"
            if len(top) > 0:
                del top[-1]
            branches[0] += 1
            Stree.append(lseq)
            Stree.append(rseq)
            top.append(lseq)
            top.append(rseq)
            found = True
            rules["RG"] += 1
            break
        dindex += 1
    return found


def close_next(sequent):
    global Stree
    global top
    global visited
    global axioms
    global rules
    found = False
    ancopy = sequent.ansc[:]
    decopy = sequent.desc[:]
    arem_upto = len(ancopy)
    drem_upto = len(decopy)
    for a in sequent.ansc:
        formula_str = str(a).replace(" ", "")
        temp = re.match(r"^X\((.*?)\)$", formula_str)
        if temp and check(temp.group(1)) == "Balanced":
            formula_str = temp.group(1)
            ancopy.append(formula_str)
            found = True

    for d in sequent.desc:
        formula_str = str(d).replace(" ", "")
        temp = re.match(r"^X\((.*?)\)$", formula_str)
        if temp and check(temp.group(1)) == "Balanced":
            formula_str = temp.group(1)
            decopy.append(formula_str)
            found = True

    if found:
        ancopy = ancopy[arem_upto:]
        decopy = decopy[drem_upto:]
        seq = Sequent(ansc=ancopy, desc=decopy)
        sequent.children = [None, seq]
        seq.parent = sequent
        seq.from_rule = "(X)"
        if seq.parent.rbox_root:
            seq.rbox_root = seq.parent.rbox_root
        Stree.append(seq)
        top.append(seq)
        visited.append(sequent)
        rules["X"] += 1
    return found


def close_saturated(sequent):
    global Stree
    global top
    global visited
    global axioms
    global closed
    empty_ansc = re.match(r"^=>([a-z]+,?)+$", repr(sequent))
    empty_desc = re.match(r"^([a-z]+,?)+=>$", repr(sequent))
    atleast_one = re.match(r"^([a-z]+,?)+=>([a-z]+,?)+$", repr(sequent))
    if len(sequent.ansc) == 0:
        if close_axiom(sequent):
            return True
        if len(sequent.desc) == 0:
            closed.append(sequent)
            visited.append(sequent)
            return True
    if empty_ansc or empty_desc:
        closed.append(sequent)
        visited.append(sequent)
        return True
    elif atleast_one:
        for a in range(len(sequent.ansc)):
            for d in sequent.desc:
                # input("ax")
                if close_axiom(sequent):
                    return True
        visited.append(sequent)
        closed.append(sequent)
        return True
    else:
        if close_axiom(sequent):
            return True
        if sequent.rbox_root:
            if close_loop_axiom(sequent):
                return True
        else:
            par = sequent.parent
            while par:
                if set([str(a).replace(" ", "") for a in sequent.ansc]) == set(
                    [str(ap).replace(" ", "") for ap in par.ansc]
                ) and set([str(d).replace(" ", "") for d in sequent.desc]) == set(
                    [str(dp).replace(" ", "") for dp in par.desc]
                ):
                    closed.append(sequent)
                    visited.append(sequent)
                    return True
                else:
                    par = par.parent
    return False


def close_loop_axiom(sequent):
    global closed
    global visited
    global axioms
    global Stree
    global top
    global loop_size_counter
    par = sequent.parent
    while par:
        a_absorbed = [False] * len(par.ansc)
        for a in range(len(par.ansc)):
            for ap in sequent.ansc:
                if str(par.ansc[a]).replace(" ", "") == str(ap).replace(" ", ""):
                    a_absorbed[a] = True
                if reduce(lambda z, b: z and b, a_absorbed, True):
                    break
            if reduce(lambda z, b: z and b, a_absorbed, True):
                break
        if reduce(lambda z, b: z and b, a_absorbed, True):
            a_absorbed = True
        else:
            par = par.parent
            continue

        d_absorbed = [False] * len(par.desc)
        for d in range(len(par.desc)):
            for dp in sequent.desc:
                if str(par.desc[d]).replace(" ", "") == str(dp).replace(" ", ""):
                    d_absorbed[d] = True
                if reduce(lambda a, b: a and b, d_absorbed, True):
                    break
            if reduce(lambda a, b: a and b, d_absorbed, True):
                break
        if reduce(lambda a, b: a and b, d_absorbed, True):
            d_absorbed = True
        else:
            par = par.parent
            continue

        def check_if_rchild(sequent, tofind):
            if not sequent:
                return False
            if sequent.children == [None, None]:
                return False
            if tofind in sequent.children:
                return True
            if check_if_rchild(sequent.children[0], tofind):
                return True
            if check_if_rchild(sequent.children[1], tofind):
                return True
            return False

        if a_absorbed and d_absorbed:
            counter = 0
            search_path = []
            par = sequent.parent
            while par:
                counter += 1
                search_path.append(par)
                if par == sequent.rbox_root:
                    break
                par = par.parent
            if len(search_path) > 0:
                if sequent.rbox_root.children[0] in search_path or not check_if_rchild(
                    sequent.rbox_root.children[1], sequent
                ):
                    return False
            else:
                return False
            loop_size_counter.append(counter)
            closed.append(sequent)
            l_axioms.append(sequent)
            visited.append(sequent)
            return True
    return False


def get_loops():
    return loop_size_counter


def max_loop():
    return max(get_loops()) if get_loops() else 0


def total_seq_comp_for_loops():
    return reduce(lambda x, y: x + y, loop_size_counter, 0)


def close_axiom(sequent):
    global axioms
    global visited
    global closed
    global top
    if len(sequent.ansc) == 0:
        if "true" in [str(d) for d in sequent.desc]:
            visited.append(sequent)
            closed.append(sequent)
            axioms.append(sequent)
            return True
    for a in range(len(sequent.ansc)):
        for d in sequent.desc:
            if str(sequent.ansc[a]).replace(" ", "") == str(d).replace(" ", ""):
                visited.append(sequent)
                closed.append(sequent)
                axioms.append(sequent)
                return True
    return False


def prast(sequent):
    seen = set()
    result = []
    for item in [str(a) for a in sequent.ansc]:
        if item not in seen:
            seen.add(item)
            result.append(item)
    sequent.ansc = result
    seen = set()
    result = []
    for item in [str(a) for a in sequent.desc]:
        if item not in seen:
            seen.add(item)
            result.append(item)
    sequent.desc = result


def solved():
    return solvedMark(closed, axioms, l_axioms)


def printSTree():
    print()
    printTree(Stree[0], closed, axioms, l_axioms)


def printAx():
    printAxioms(axioms)


def printLAx():
    printLAxioms(l_axioms)


def get_rules():
    return rules
