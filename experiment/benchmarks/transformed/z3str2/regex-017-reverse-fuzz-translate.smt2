(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "@I") (re.++ (str.to.re ">}jwm") (str.to.re "_4lao"))))))
(assert (= 10 (str.len x)))
(check-sat)
(get-model)
