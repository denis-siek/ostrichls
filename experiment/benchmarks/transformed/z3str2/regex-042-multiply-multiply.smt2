(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "aaaa") (re.* (str.to.re "bbbb")))))
(assert (str.in.re x (re.++ (str.to.re "aaaa") (re.++ (re.* (str.to.re "bbbb")) (re.* (str.to.re "cccc"))))))
(assert (= 12 (str.len x)))
(check-sat)
(get-model)
