(declare-const x String)
(assert (= x "p%#ccb"))
(assert (str.in.re x (re.++ (str.to.re "?7>c") (re.+ (str.to.re "dcb,)")))))
(check-sat)
(get-model)
