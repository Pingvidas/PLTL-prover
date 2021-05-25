#!/usr/bin/python

from copy import deepcopy as copy


def remove_text_inside_brackets(text, brackets="()"):
    countor = 0
    indexor = 0
    countand = 0
    indexand = 0
    countimp = 0
    indeximp = 0
    index = 0
    count = [0] * (len(brackets) // 2)  # count open/close brackets
    saved_chars = []
    for character in text:
        if character == "|":
            countor += 1
        if character == "&":
            countand += 1
        if character == "-":
            countimp += 1
        for i, b in enumerate(brackets):
            if character == b:  # found bracket
                kind, is_close = divmod(i, 2)
                count[kind] += (-1) ** is_close  # `+1`: open, `-1`: close
                if count[kind] < 0:  # unbalanced bracket
                    count[kind] = 0  # keep it
                else:  # found bracket to remove
                    break
        else:  # character is not a [balanced] bracket
            if not any(count):  # outside brackets
                saved_chars.append(character)
                if character == "|":
                    indexor = index
                if character == "&":
                    indexand = index
                if character == "-":
                    indeximp = index
        index += 1
    return ["".join(saved_chars), indexor, indexand, indeximp]


def check(myStr):
    stack = []
    for i in myStr:
        if i == "(":
            stack.append(i)
        elif i == ")":
            if (len(stack) > 0) and ("(" == stack[len(stack) - 1]):
                stack.pop()
            else:
                return "Unbalanced"
    if len(stack) == 0:
        return "Balanced"
    else:
        return "Unbalanced"


def printVisited(visited_list):
    print("visited: ")
    for s in visited_list:
        print(s)
    print()


def printAxioms(a_list):
    axioms_list = copy(a_list)
    print("Axioms: ")
    for inx, s in enumerate(axioms_list):
        print(f"{inx+1:2}. {s}", end="")
        a = s.parent
        while a:
            print(f" | {a}", end="")
            a = a.parent
        print()
    print()


def printLAxioms(la_list):
    l_axioms_list = copy(la_list)
    print("Loop axioms: ")
    for inx, s in enumerate(l_axioms_list):
        print(f"{inx+1:2}. {s}", end="")
        a = s.parent
        while a:
            print(f" | {a}", end="")
            a = a.parent
            if (
                a
                and set([str(an).replace(" ", "") for an in s.ansc])
                == set([str(ap).replace(" ", "") for ap in a.ansc])
                and set([str(d).replace(" ", "") for d in s.desc])
                == set([str(dp).replace(" ", "") for dp in a.desc])
            ):
                print(f" | {a}", end="")
                break
        print()
    print()


def printClosed(c_list):
    closed_list = copy(c_list)
    print("Closed: ")
    for inx, s in enumerate(closed_list):
        print(f"{inx+1:2}. {s}", end="")
        a = s.parent
        while a:
            print(f" | {a}", end="")
            a = a.parent
        print()
    print()


def solvedMark(closed_list, axioms_list, l_axioms_list):
    if set(closed_list) == (set(axioms_list).union(set(l_axioms_list))):
        return "SOLVED"
    else:
        return "UNSOLVED"


def longest_path(closed_list):
    lpath = 0
    for c in closed_list:
        par = c.parent
        local_path = 0
        while par:
            local_path += 1
            par = par.parent
        lpath = max(lpath, local_path)
    return lpath


def printTree(root, closed, axioms, l_axioms, markerStr="---- ", levelMarkers=[]):
    if root == None:
        return
    emptyStr = " " * len(markerStr)
    connectionStr = "|" + emptyStr[:-1]
    level = len(levelMarkers)
    mapper = lambda draw: connectionStr if draw else emptyStr
    markers = "".join(map(mapper, levelMarkers[:-1]))
    rule = "+"
    if root.parent:
        if root.parent.children[0] == root:
            rule = root.from_rule
        elif root.parent.children[1] == root and root.parent.children[0] == None:
            rule = root.from_rule
    markers += f"{rule}{markerStr}" if level > 0 else ""
    axiom_marker = ""
    if str(root) in [str(c) for c in closed] and root.children == [None, None]:
        classic = False
        loop = False
        for a in axioms:
            if root == a:
                classic = True
                axiom_marker = " (+)"
                break
        if not classic:
            for a in l_axioms:
                if root == a:
                    loop = True
                    axiom_marker = " (+L)"
                    break
        if not classic and not loop:
            axiom_marker = " (-)"

    print(f"  {markers}{root}{axiom_marker}")
    mapper = lambda draw: connectionStr if draw else emptyStr
    markers = "".join(map(mapper, levelMarkers[:-1]))
    print(f"  {markers}")
    for i, child in enumerate(root.children):
        isLast = i == len(root.children) - 1
        printTree(
            child, closed, axioms, l_axioms, markerStr, [*levelMarkers, not isLast]
        )
