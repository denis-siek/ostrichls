(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "'''\t''\t''''''\t''\t'''")) (str.to.re "pppp")))))
(assert (= (str.len x) 12))
(assert (not (= x "'''\t''\t''''''\t''\t''''''\t''\t''''''\t''\t'''pppp")))
(assert (not (= x "'''\t''\t''''''\t''\t'''pppppppp")))
(assert (not (= x "pppp'''\t''\t''''''\t''\t'''pppp")))
(check-sat)
(get-model)
