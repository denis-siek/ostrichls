(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (not (str.in.re x (re.+ (str.to.re "cP")))))
(assert (= x "4'\t';x;"))
(check-sat)
(get-model)
