(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "") (str.to.re "21")))))
(assert (= 1 (str.len x)))
(assert (not (= x "/$31")))
(check-sat)
(get-model)
