(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "!j[<WcF7;"))))
(assert (str.in.re y (re.* (str.to.re "nZt'\x0c'""L""?&?;0L|""xP[*0B"))))
(assert (= (str.to.int x) 14))
(check-sat)
(get-model)
