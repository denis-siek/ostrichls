(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "''\n''"))))
(assert (= 5 (str.len x)))
(assert (not (= x "''\n''''\n''''\n''''\n''''\n''")))
(check-sat)
(get-model)
