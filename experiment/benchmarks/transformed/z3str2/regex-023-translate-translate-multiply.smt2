(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "pp")) (str.to.re "'''\x0b''\x0b'''")))))
(assert (> (str.len x) 0))
(check-sat)
(get-model)
