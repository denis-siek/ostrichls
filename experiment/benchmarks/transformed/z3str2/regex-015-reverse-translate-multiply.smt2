(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "2211``'''\r''\r'''"))))
(assert (str.in.re y (re.* (re.* (str.to.re "2211``'''\r''\r'''")))))
(assert (= (str.len x) 8))
(assert (= (str.len y) 16))
(check-sat)
(get-model)
