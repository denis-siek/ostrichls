(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "'\t''\t''\t''\t'MMMM"))))
(assert (str.in.re x (re.* (str.to.re "'\t''\t''\t''\t'MMMM'\t''\t''\t''\t'MMMM"))))
(assert (str.in.re x (re.* (str.to.re "'\t''\t''\t''\t'MMMM'\t''\t''\t''\t'MMMM'\t''\t''\t''\t'wwww"))))
(check-sat)
(get-model)
