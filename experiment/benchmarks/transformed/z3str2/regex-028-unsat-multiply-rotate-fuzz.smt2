(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "aWIp5xB"))))
(assert (str.in.re x (re.+ (str.to.re "aM~hbGR.!J'\x0b'@N"))))
(assert (str.in.re x (re.+ (str.to.re "^o-$1V~5#g#iGWba@'iofX^%dsPac5}Y@Y+D'\t':u'\n'cc"))))
(assert (> (str.len x) 1))
(check-sat)
(get-model)
