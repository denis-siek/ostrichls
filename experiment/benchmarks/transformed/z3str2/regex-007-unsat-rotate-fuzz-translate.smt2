(declare-const x String)
(assert (= (str.len x) 2))
(assert (str.in.re x (re.* (str.to.re "5'\r'"))))
(assert (str.in.re x (re.* (str.to.re "I_'\t'P"))))
(check-sat)
(get-model)
