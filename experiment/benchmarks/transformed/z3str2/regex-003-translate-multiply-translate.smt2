(declare-const x String)
(assert (= x "!!!'\n'!!'\n'!!!'\r''\r'YY}}pp!!!'\n'!!'\n'!!!'\r''\r'!!!'\n'!!'\n'!!!'\r''\r'YY"))
(assert (str.in.re x (re.* (re.union (str.to.re "}}pp!!!'\n'!!'\n'!!!'\r''\r'") (str.to.re "!!!'\n'!!'\n'!!!'\r''\r'YY")))))
(check-sat)
(get-model)
