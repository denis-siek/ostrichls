(declare-const x String)
(assert (= x "rQc{c{%"))
(assert (str.in.re x (re.union (re.* (str.to.re "rQc{")) (re.* (str.to.re "c{%")))))
(check-sat)
(get-model)
