include('Axioms/zfc.ax').
include('Axioms/definitions.p').
%empty set is empty
fof(emptysetisempty, conjecture, ![X]: ~member(X, null_class)).
