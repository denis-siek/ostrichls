(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (re.* (str.to.re "L")) (re.* (str.to.re "L")))))
(assert (str.in.re x (re.++ (re.++ (re.* (str.to.re "s")) (str.to.re ",")) (str.to.re ","))))
(assert (= (str.len x) 3))
(check-sat)
(get-model)
