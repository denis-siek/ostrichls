(declare-const x String)
(declare-const y String)
(assert (= x "''' '' '''GGHH'''\r''\r'''~~00yy__SSkk``::"))
(assert (str.in.re x (re.* (str.to.re ""))))
(check-sat)
(get-model)
