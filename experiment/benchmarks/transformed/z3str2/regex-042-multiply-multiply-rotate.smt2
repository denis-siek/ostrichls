(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "bbbb") (re.* (str.to.re "aaaa")))))
(assert (str.in.re x (re.++ (re.* (re.* (str.to.re "cccc"))) (re.++ (str.to.re "bbbb") (str.to.re "aaaa")))))
(assert (= 12 (str.len x)))
(check-sat)
(get-model)
