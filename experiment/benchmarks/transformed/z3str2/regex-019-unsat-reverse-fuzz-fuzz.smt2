(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "'"))))
(assert (= 0 (str.to.int x)))
(assert (not (= x "&?4*Z2Yl[NN[a")))
(check-sat)
(get-model)
