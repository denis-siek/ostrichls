(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "8e>l"))))
(assert (= (str.len x) 2))
(check-sat)
(get-model)
