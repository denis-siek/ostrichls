(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "a"))))
(assert (= 3 (str.len x)))
(assert (not (= x "aa<")))
(assert (not (= x "a<<")))
(assert (not (= x "<a<")))
(check-sat)
(get-model)
