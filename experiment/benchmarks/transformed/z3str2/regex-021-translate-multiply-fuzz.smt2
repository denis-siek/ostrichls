(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.* (str.to.re "X<'\x0c'")) (str.to.re "s")))))
(assert (= (str.to.int x) 8))
(check-sat)
(get-model)
