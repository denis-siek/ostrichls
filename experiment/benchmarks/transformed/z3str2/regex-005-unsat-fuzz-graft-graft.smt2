(declare-const x String)
(declare-const y String)
(assert (= x "aaa_%),kna"))
(assert (str.in.re x (str.to.re "cd")))
(check-sat)
(get-model)
