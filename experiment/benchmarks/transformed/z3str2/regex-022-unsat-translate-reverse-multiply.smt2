(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "'''''\n''\n'''''") (re.* (str.to.re "<<"))))))
(assert (= (str.len x) 4))
(assert (not (= x "'''''\n''\n''''''''''\n''\n'''''")))
(assert (not (= x "'''''\n''\n'''''<<")))
(check-sat)
(get-model)
