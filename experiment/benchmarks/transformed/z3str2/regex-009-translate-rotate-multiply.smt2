(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "''''' '' '''''..ssFF"))))
(assert (str.in.re x (re.* (str.to.re "''''' '' '''''..ssFF''''' '' '''''..ssFF"))))
(assert (> (str.len x) 40))
(assert (< (str.len x) 50))
(check-sat)
(get-model)
