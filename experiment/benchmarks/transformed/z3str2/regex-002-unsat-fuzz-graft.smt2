(declare-const x String)
(declare-const y String)
(assert (= x "F''\x0b''xL|a[Hy''\x0c''#}lRs'' ''e/1''\x0c''a"))
(assert (str.in.re x (str.to.re "''\n''e")))
(check-sat)
(get-model)
