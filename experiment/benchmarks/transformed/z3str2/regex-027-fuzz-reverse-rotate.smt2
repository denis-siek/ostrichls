(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (re.* (str.to.re "")) (str.to.re "C")))))
(assert (= (str.to.int x) 5))
(assert (not (= x "we|")))
(assert (not (= x "bOw")))
(assert (not (= x "O{\\A?")))
(check-sat)
(get-model)
