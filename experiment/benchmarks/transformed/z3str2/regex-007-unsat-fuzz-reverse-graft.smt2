(declare-const x String)
(assert (= 13 (str.to.int x)))
(assert (str.in.re x (re.+ (str.to.re "O"))))
(assert (str.in.re x (str.to.re "'''\t'''soV")))
(check-sat)
(get-model)
