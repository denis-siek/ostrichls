(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.+ (re.union (str.to.re "H") (str.to.re ")")))))
(assert (= 5 (str.to.int x)))
(assert (not (= x "<")))
(assert (not (= x "|DxAv6yfa")))
(assert (not (= x ",'OAJ'")))
(assert (not (= x "")))
(assert (not (= x "")))
(assert (not (= x "b[z/K6hU")))
(assert (not (= x "<a")))
(check-sat)
(get-model)
