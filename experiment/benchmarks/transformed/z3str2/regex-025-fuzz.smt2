(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.* (str.to.re "'\x0b'")) (str.to.re "")))))
(assert (str.in.re y (re.+ (re.union (re.+ (str.to.re "a")) (str.to.re "")))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= (str.to.int x) 9))
(check-sat)
(get-model)
