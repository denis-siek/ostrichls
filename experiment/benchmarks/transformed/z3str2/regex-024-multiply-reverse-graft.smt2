(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.++ (str.to.re "bb") (re.* (str.to.re "aa"))) (re.* (str.to.re "aa"))))))
(assert (str.in.re y (re.* (str.to.re "bb"))))
(check-sat)
(get-model)
