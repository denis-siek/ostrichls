(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re ""))))
(assert (str.in.re x (re.* (str.to.re "$>$'\t'f!"))))
(assert (str.in.re x (re.* (str.to.re "`Rti'\n'BFELv"))))
(check-sat)
(get-model)
