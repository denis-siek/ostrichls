(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.+ (str.to.re "U")) (str.to.re "'")))))
(assert (= (str.len x) 0))
(assert (not (= x "'7*FFY!@'>Yx;'WI*']J")))
(assert (not (= x "'~'\n''")))
(check-sat)
(get-model)
