(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "x") (str.to.re "a")))))
(assert (= 3 (str.len x)))
(assert (not (= x "xxa")))
(assert (not (= x "xax")))
(assert (not (= x "xaa")))
(check-sat)
(get-model)
