(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "eFb?"))))
(assert (str.in.re x (re.+ (str.to.re "D1J'abZXvibb"))))
(assert (str.in.re x (re.* (str.to.re "a/iLkt'SRr#bbAHt,lC#b\\;E}5O''\r''&C?0c"))))
(check-sat)
(get-model)
