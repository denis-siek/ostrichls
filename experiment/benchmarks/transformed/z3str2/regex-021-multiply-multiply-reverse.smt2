(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "bbbb") (re.* (str.to.re "aaaa"))))))
(assert (= (str.len x) 8))
(check-sat)
(get-model)
