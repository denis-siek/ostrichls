(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "la'\n'cI8'\r''\x0b'@\\") (str.to.re "12")))))
(assert (= 2 (str.len x)))
(check-sat)
(get-model)
