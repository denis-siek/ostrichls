(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re ""))))
(assert (str.in.re x (re.+ (str.to.re "o' 'H"))))
(assert (str.in.re x (re.* (str.to.re "Xd;'' 'y"))))
(assert (> (str.to.int x) 0))
(check-sat)
(get-model)
