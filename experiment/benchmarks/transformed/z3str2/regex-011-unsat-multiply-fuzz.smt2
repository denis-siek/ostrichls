(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "bUqO]c"))))
(assert (str.in.re y (re.* (str.to.re "QbbZgVcd"))))
(assert (= (str.len x) 22))
(check-sat)
(get-model)
