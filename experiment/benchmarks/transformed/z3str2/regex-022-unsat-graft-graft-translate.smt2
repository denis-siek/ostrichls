(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "%")))
(assert (= (str.len x) 2))
(assert (not (= x "<<")))
(assert (not (= x "%<")))
(check-sat)
(get-model)
