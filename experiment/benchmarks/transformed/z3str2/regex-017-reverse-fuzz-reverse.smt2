(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "AB") (re.++ (str.to.re ";I!4\\") (str.to.re "^sowd"))))))
(assert (= 10 (str.len x)))
(check-sat)
(get-model)
