(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.* (str.to.re "p")) (str.to.re ",")))))
(assert (str.in.re y (re.* (re.union (re.* (str.to.re "!")) (str.to.re "p")))))
(check-sat)
(get-model)
