(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (re.* (str.to.re "LL")) (str.to.re "rr"))))
(assert (str.in.re x (re.++ (re.* (str.to.re "II")) (str.to.re "II"))))
(assert (str.in.re x (re.++ (re.++ (re.* (str.to.re "II")) (re.* (str.to.re "LL"))) (str.to.re "rr"))))
(check-sat)
(get-model)
