(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "") (re.* (str.to.re "|a")))))
(assert (str.in.re x (re.++ (re.* (re.+ (str.to.re "cc"))) (re.union (str.to.re "9b") (str.to.re "aB")))))
(assert (= 8 (str.to.int x)))
(check-sat)
(get-model)
