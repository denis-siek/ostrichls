(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "BB'''\t''\t'''zz""""||CC||||~~||II"))))
(assert (str.in.re y (re.* (str.to.re "NN"))))
(assert (= (str.to.int x) 18))
(check-sat)
(get-model)
