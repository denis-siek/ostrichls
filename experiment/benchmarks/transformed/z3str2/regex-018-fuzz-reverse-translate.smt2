(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "2-I##""##") (str.to.re "Z%")))))
(assert (= 8 (str.to.int x)))
(assert (not (= x "ZlVm,U~##|##91")))
(check-sat)
(get-model)
