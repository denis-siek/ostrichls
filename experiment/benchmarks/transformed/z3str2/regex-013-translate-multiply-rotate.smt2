(declare-const x String)
(declare-const y String)
(assert (str.in.re y (re.* (re.* (str.to.re "``]]AA''''\x0c''''\x0c''''")))))
(assert (= (str.len y) 16))
(check-sat)
(get-model)
