(declare-const x String)
(declare-const y String)
(assert (str.in.re y (str.to.re "``]]AA'''''\x0c''\x0c'''''")))
(assert (= 16 (str.len y)))
(check-sat)
(get-model)
