(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "&") (re.* (str.to.re "k")))))
(assert (str.in.re x (re.++ (str.to.re "j") (re.* (str.to.re "j")))))
(assert (str.in.re x (re.++ (str.to.re "j") (re.* (re.* (re.++ (str.to.re "k") (str.to.re "&")))))))
(check-sat)
(get-model)
