(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "'\n'") (re.* (str.to.re "V"))))))
(assert (> (str.to.int x) 0))
(check-sat)
(get-model)
