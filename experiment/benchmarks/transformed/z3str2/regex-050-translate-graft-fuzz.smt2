(declare-const x String)
(declare-const y String)
(assert (= 2 (str.to.int x)))
(assert (= x y))
(assert (str.in.re y (re.* (re.range "a" "b"))))
(assert (str.prefixof "1" x))
(check-sat)
(get-model)
