(declare-const x String)
(assert (= 7 (str.len x)))
(assert (str.in.re x (str.to.re "'\r'Z2K")))
(assert (str.in.re x (re.* (re.* (str.to.re "c/")))))
(check-sat)
(get-model)
