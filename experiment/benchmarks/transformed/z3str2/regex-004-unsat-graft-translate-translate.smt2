(declare-const x String)
(assert (= x ")Gj'\x0c'j'\x0c'N"))
(assert (str.in.re x (re.union (re.* (re.* (str.to.re "j'\x0c'N"))) (str.to.re ")Gj'\x0c'"))))
(check-sat)
(get-model)
