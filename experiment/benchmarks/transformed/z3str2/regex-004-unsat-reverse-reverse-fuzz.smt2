(declare-const x String)
(assert (= x "'\x0b'Q}>Dy='\n'X$c'\r'b&Or_rts"))
(assert (str.in.re x (re.union (re.* (str.to.re "ab'\x0b')CU")) (re.* (str.to.re "cOW")))))
(check-sat)
(get-model)
