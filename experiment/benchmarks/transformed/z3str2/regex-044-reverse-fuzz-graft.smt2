(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.+ (re.range "0" "9"))))
(assert (= (str.len x) 0))
(assert (not (= x "")))
(assert (not (= x "&")))
(assert (not (= x "3")))
(assert (not (= x "J")))
(assert (not (= x "")))
(assert (not (= x "")))
(assert (not (= x "")))
(assert (not (= x "")))
(assert (not (= x "I")))
(check-sat)
(get-model)
