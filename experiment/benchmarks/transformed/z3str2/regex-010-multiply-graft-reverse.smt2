(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "bbaa"))))
(assert (str.in.re x (re.* (re.* (str.to.re "ccaabbaabbaa")))))
(assert (str.in.re x (str.to.re "bbaabbaa")))
(check-sat)
(get-model)
