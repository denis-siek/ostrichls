(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "||'''\x0c''\x0c'''iizz"))))
(assert (str.in.re x (re.* (str.to.re "||'''\x0c''\x0c'''iizz||'''\x0c''\x0c'''iizz"))))
(assert (> (str.len x) 40))
(assert (< (str.len x) 50))
(check-sat)
(get-model)
