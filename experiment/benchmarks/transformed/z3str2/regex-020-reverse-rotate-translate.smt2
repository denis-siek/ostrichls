(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "~") (re.* (str.to.re "O"))))))
(assert (= (str.len x) 3))
(assert (not (= x "OO~")))
(assert (not (= x "O~O")))
(assert (not (= x "O~~")))
(check-sat)
(get-model)
