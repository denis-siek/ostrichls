(declare-const S String)
(assert (str.in.re S (re.union (str.to.re "Qg,Vb''\r''") re.allchar)))
(assert (not (str.in.re S (re.union (re.union (str.to.re "*ih3k''\x0c''") (str.to.re "b8uJ")) re.allchar))))
(check-sat)
(get-model)
