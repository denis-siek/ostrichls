(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "w") (re.union (str.to.re ";") (str.to.re "wB"))))))
(assert (= 1 (str.len x)))
(check-sat)
(get-model)
