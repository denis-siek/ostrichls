(declare-const x String)
(declare-const y String)
(assert (= 1 (str.len x)))
(assert (= x y))
(assert (str.in.re y (re.* (re.range "a" "b"))))
(assert (str.suffixof "" x))
(check-sat)
(get-model)
