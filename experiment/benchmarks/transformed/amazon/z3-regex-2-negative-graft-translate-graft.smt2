(declare-const S String)
(assert (str.in.re S (str.to.re ")))///")))
(assert (not (str.in.re S (str.to.re "///"))))
(check-sat)
(get-model)
