(declare-const x String)
(declare-const y String)
(assert (= x "yyyyyyyyy"))
(assert (str.in.re x (re.* (str.to.re "+zu"))))
(check-sat)
(get-model)
