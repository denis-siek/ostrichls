(declare-const x String)
(assert (= 8 (str.len x)))
(assert (str.in.re x (str.to.re "'' ''b%M")))
(assert (str.in.re x (re.* (re.* (str.to.re "%nM")))))
(check-sat)
(get-model)
