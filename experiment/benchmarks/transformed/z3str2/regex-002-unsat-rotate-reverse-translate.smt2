(declare-const x String)
(declare-const y String)
(assert (= x "JJJJJJJJJ"))
(assert (str.in.re x (re.* (str.to.re "LDE"))))
(check-sat)
(get-model)
