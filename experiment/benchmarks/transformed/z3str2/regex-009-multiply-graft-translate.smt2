(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "VV'\x0b''\x0b'((yyVV'\x0b''\x0b'((yy")))
(assert (str.in.re x (re.* (re.* (str.to.re "VV'\x0b''\x0b'((yy")))))
(assert (> 40 (str.len x)))
(assert (< (str.len x) 50))
(check-sat)
(get-model)
