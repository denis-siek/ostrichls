(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "}}RR"))))
(assert (str.in.re x (re.+ (str.to.re "99WWrr"))))
(assert (str.in.re x (re.* (str.to.re "``'''\x0b''\x0b'''xx'''\n''\n'''VV55yyppdd$$@@11""""WWEE"))))
(check-sat)
(get-model)
