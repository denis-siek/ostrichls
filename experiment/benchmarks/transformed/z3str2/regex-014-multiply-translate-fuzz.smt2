(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "Fc*QE!'\t':"))))
(assert (str.in.re y (re.+ (str.to.re "'\x0c'(4'\r'i@oWyl<>"))))
(assert (= (str.len x) 0))
(assert (= (str.len y) 16))
(check-sat)
(get-model)
