(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re ""))))
(assert (= 16 (str.len x)))
(assert (not (= x "//ll````==ee..||'''\n''\n'''**")))
(check-sat)
(get-model)
