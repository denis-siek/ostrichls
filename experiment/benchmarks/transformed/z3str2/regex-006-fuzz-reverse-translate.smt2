(declare-const x String)
(declare-const y String)
(assert (= x "~~+T4&"))
(assert (str.in.re x (re.* (re.+ (str.to.re "?9a")))))
(check-sat)
(get-model)
