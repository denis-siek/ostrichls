(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (re.* (str.to.re "a")) (str.to.re "b"))))
(assert (str.in.re x (re.++ (re.* (str.to.re "c")) (str.to.re "c"))))
(assert (str.in.re x (re.++ (str.to.re "a") (re.* (re.* (str.to.re "c"))))))
(check-sat)
(get-model)
