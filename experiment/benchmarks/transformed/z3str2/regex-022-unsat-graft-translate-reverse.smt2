(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "y")) (str.to.re "<")))))
(assert (= 2 (str.len x)))
(assert (not (= x "<<")))
(assert (not (= x "<y")))
(check-sat)
(get-model)
