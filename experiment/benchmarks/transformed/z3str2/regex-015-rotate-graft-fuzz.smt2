(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "Z(NR2")))
(assert (str.in.re y (re.+ (re.* (str.to.re "*`]y*o2")))))
(assert (= (str.len x) 2))
(assert (= 16 (str.to.int y)))
(check-sat)
(get-model)
