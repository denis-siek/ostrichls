(declare-const x String)
(declare-const y String)
(assert (= x "cccccccccccccccccc"))
(assert (str.in.re x (re.* (re.* (str.to.re "^^::DD")))))
(check-sat)
(get-model)
