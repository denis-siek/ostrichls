(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.* (str.to.re "aa")) (str.to.re "")))))
(assert (= (str.to.int x) 0))
(check-sat)
(get-model)
