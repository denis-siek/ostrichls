(declare-const x String)
(assert (= x "a>U|8@],c+kGi.L%' 'A0v'\r''' 'k'\r'fdcc4TBAB*ye"))
(assert (str.in.re x (re.union (re.* (re.+ (str.to.re "c'\r'}Sx'\x0b'"))) (str.to.re "'\t')G""[ab,zd"))))
(check-sat)
(get-model)
