(declare-const x String)
(assert (= x "edcdcbaedc"))
(assert (str.in.re x (str.to.re "edc")))
(check-sat)
(get-model)
