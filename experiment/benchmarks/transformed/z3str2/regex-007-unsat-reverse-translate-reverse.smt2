(declare-const x String)
(assert (= (str.len x) 8))
(assert (str.in.re x (re.* (str.to.re "NCU"))))
(assert (str.in.re x (re.* (str.to.re "''\r''kNU"))))
(check-sat)
(get-model)
