(declare-const x String)
(assert (str.in.re x (str.to.re "a@#")))
(assert (> (str.len x) 3))
(check-sat)
