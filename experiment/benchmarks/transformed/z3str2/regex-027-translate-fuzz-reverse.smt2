(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.* (str.to.re "Y")) (str.to.re "}")))))
(assert (= (str.len x) 2))
(assert (not (= x "KWjY")))
(assert (not (= x "L._TY")))
(assert (not (= x "LY")))
(check-sat)
(get-model)
