include('Axioms/zfc.ax').
include('Axioms/definitions.p').
%domain of identity function is X
cnf(domid, negated_conjecture, domain_of(ident_fun(X))!=X).
