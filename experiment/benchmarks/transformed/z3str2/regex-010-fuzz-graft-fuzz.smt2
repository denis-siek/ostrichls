(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "t&"))))
(assert (str.in.re x (re.* (re.* (str.to.re "\\^$/o")))))
(assert (str.in.re x (str.to.re "bw")))
(check-sat)
(get-model)
