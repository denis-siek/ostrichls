(declare-const x String)
(declare-const y String)
(assert (= x "TM{S{M^m/w{+{-mmmmmm"))
(assert (str.in.re x (re.* (re.* (str.to.re "$' '")))))
(check-sat)
(get-model)
