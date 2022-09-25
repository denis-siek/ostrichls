(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "~V~:~~h~"))))
(assert (str.in.re x (re.* (str.to.re "~V~:~~h~~V~:~~h~"))))
(assert (> (str.len x) 20))
(assert (< (str.len x) 25))
(check-sat)
(get-model)
