(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "X") (re.* (str.to.re "s"))))))
(assert (= (str.len x) 2))
(check-sat)
(get-model)
