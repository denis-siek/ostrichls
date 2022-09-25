(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.union (str.to.re ",,") (str.to.re "jj")))))
(assert (= 6 (str.len x)))
(assert (not (= x ",,jjjj")))
(assert (not (= x ",,jj,,")))
(assert (not (= x "jjjj,,")))
(assert (not (= x "jjjjjj")))
(assert (not (= x "jj,,,,")))
(assert (not (= x "jj,,jj")))
(assert (not (= x ",,,,,,")))
(check-sat)
(get-model)
