(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "7N"))))
(assert (= (str.to.int x) 9))
(check-sat)
(get-model)
