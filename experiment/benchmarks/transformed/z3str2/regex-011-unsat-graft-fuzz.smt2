(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "acd")))
(assert (str.in.re y (re.+ (re.+ (str.to.re "zI}ucd")))))
(assert (= 7 (str.to.int x)))
(check-sat)
(get-model)
