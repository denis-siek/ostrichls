(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re ":$a\\QKJcO+j"))))
(assert (str.in.re y (re.+ (str.to.re "a'|"))))
(assert (= (str.to.int x) 1))
(check-sat)
(get-model)
