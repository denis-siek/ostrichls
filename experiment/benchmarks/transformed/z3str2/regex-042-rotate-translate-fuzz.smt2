(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "!'\t'") (re.+ (str.to.re "%")))))
(assert (str.in.re x (re.union (re.+ (re.* (str.to.re "("))) (re.union (str.to.re "'\t''") (str.to.re ";")))))
(assert (= 6 (str.to.int x)))
(check-sat)
(get-model)
