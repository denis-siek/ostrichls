(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "uuuu")) (str.to.re ",,,,")))))
(assert (str.in.re y (re.* (re.++ (re.* (str.to.re "uuuu")) (str.to.re ",,,,")))))
(check-sat)
(get-model)
