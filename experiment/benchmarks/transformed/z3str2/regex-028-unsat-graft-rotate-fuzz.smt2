(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "b"))))
(assert (str.in.re x (re.* (re.* (str.to.re "&+/a9s")))))
(assert (str.in.re x (str.to.re "a{la")))
(assert (> 0 (str.to.int x)))
(check-sat)
(get-model)
