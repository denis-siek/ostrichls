(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "'''\n''\n'''"))))
(assert (= 0 (str.len x)))
(assert (not (= x "zz//aarr[[..")))
(check-sat)
(get-model)
