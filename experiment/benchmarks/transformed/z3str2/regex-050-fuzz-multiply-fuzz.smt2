(declare-const x String)
(declare-const y String)
(assert (= (str.len x) 0))
(assert (= x y))
(assert (str.in.re y (re.+ (re.range "a" "b"))))
(assert (str.contains "16" x))
(check-sat)
(get-model)
