(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "nn")))
(assert (= 6 (str.len x)))
(assert (not (= x "PPnnnn")))
(assert (not (= x "nnPPnn")))
(assert (not (= x "PPPPnn")))
(check-sat)
(get-model)
