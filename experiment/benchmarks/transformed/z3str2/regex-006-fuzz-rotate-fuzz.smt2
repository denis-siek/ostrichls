(declare-const x String)
(declare-const y String)
(assert (= x "*b;"))
(assert (str.in.re x (re.+ (re.+ (str.to.re "x^g")))))
(check-sat)
(get-model)
