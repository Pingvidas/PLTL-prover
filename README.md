# PLTL-prover
Sequent prover for PLTL logic
./solver formula|sequent [-v|-t] [help]
formula - formula in PLTL form
sequent - sequent in PLTL form
Atoms are lowercase letters a-z
Accepted binary operators: ->, V, &
Accepted unary (and modal) operators: ~, G, X
Special keyword: T - Tautology. T = (p|~p)
Example PLTL formula: "(a->(b&T)) & ~(cVd) | G(e&f) -> X a"
Sequent form: f1, ..., fn => g1, ..., gm, where fi and gi are PLTL formulas
-v - verbose mode - print number of branches, longest path, etc.
-t - print proof tree
help - display this text
