(declare-const x String)
(declare-const y String)
(assert (= x "DDDDDDDDD"))
(assert (str.in.re x (re.* (str.to.re "ze."))))
(check-sat)
(get-model)
