(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.* (str.to.re "")) (str.to.re "bbbb")))))
(assert (str.in.re y (re.* (re.++ (re.+ (str.to.re "^^^^")) (str.to.re "bbbb")))))
(check-sat)
(get-model)
