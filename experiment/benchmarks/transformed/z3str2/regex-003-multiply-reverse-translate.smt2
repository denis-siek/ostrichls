(declare-const x String)
(assert (= x "'\x0b''\x0b'ee||ee||wwJJ'\x0b''\x0b'ee||"))
(assert (str.in.re x (re.* (re.union (str.to.re "ee||wwJJ") (str.to.re "'\x0b''\x0b'ee||")))))
(check-sat)
(get-model)
