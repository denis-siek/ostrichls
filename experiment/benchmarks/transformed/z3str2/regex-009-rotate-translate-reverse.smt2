(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "zi''\x0c''|"))))
(assert (str.in.re x (re.* (str.to.re "zi''\x0c''|zi''\x0c''|"))))
(assert (> (str.len x) 20))
(assert (< (str.len x) 25))
(check-sat)
(get-model)
