(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.* (str.to.re "o;")) (str.to.re "a")))))
(assert (str.in.re y (re.* (re.++ (re.+ (str.to.re "z]%r")) (str.to.re "a.")))))
(check-sat)
(get-model)
