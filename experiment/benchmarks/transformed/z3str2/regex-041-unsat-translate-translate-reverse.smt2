(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (re.* (str.to.re "I")) (str.to.re "{"))))
(assert (str.in.re x (re.++ (re.* (str.to.re "u")) (str.to.re "u"))))
(assert (str.in.re x (re.++ (re.++ (re.* (str.to.re "u")) (re.* (str.to.re "I"))) (str.to.re "{"))))
(check-sat)
(get-model)
