(declare-const x String)
(declare-const y String)
(assert (= x "ooooooooo"))
(assert (str.in.re x (re.* (re.* (str.to.re "^Dw")))))
(check-sat)
(get-model)
