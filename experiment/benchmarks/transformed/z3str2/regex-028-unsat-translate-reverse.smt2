(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "h~"))))
(assert (str.in.re x (re.* (str.to.re "h~h~"))))
(assert (str.in.re x (re.* (str.to.re "l~h~h~"))))
(assert (> (str.len x) 1))
(check-sat)
(get-model)
