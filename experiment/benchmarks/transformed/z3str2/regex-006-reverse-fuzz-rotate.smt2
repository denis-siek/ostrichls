(declare-const x String)
(declare-const y String)
(assert (= x "ca(^!2b%"))
(assert (str.in.re x (re.* (re.* (str.to.re "3b!p")))))
(check-sat)
(get-model)
