(declare-const x String)
(assert (= x "w'''\x0b''''''\r'''h'''\r'''h{"))
(assert (str.in.re x (re.union (str.to.re "'''\r'''h{") (re.* (str.to.re "w'''\x0b''''''\r'''h")))))
(check-sat)
(get-model)
