(declare-const x String)
(assert (= (str.to.int x) 16))
(assert (str.in.re x (re.+ (str.to.re "..NNFF(("))))
(assert (str.in.re x (re.* (str.to.re "PP--''--'''\x0b''\x0b''';;$$"))))
(check-sat)
(get-model)
