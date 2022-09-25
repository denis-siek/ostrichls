(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.range "0" "9"))))
(assert (= 0 (str.len x)))
(assert (not (= x "")))
(assert (not (= x "AA")))
(assert (not (= x "33")))
(assert (not (= x "UU")))
(assert (not (= x "")))
(assert (not (= x "")))
(assert (not (= x "]]")))
(assert (not (= x "")))
(assert (not (= x "zz")))
(check-sat)
(get-model)
