(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.* (str.to.re "a")) (str.to.re "|")))))
(assert (= (str.len x) 1))
(assert (not (= x "C|'\r'")))
(assert (not (= x "!Tb")))
(assert (not (= x "a056m")))
(check-sat)
(get-model)
