(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "+")) (str.to.re "'\n'")))))
(assert (= (str.to.int x) 1))
(assert (not (= x "d")))
(assert (not (= x "")))
(check-sat)
(get-model)
