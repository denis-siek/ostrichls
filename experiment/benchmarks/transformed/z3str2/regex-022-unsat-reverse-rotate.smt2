(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "a") (re.* (str.to.re "b"))))))
(assert (= (str.len x) 2))
(assert (not (= x "bb")))
(assert (not (= x "ba")))
(check-sat)
(get-model)
