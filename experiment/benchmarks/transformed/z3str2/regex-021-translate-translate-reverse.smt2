(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "H") (re.* (str.to.re ","))))))
(assert (= (str.len x) 2))
(check-sat)
(get-model)
