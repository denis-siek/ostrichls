(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.union (str.to.re "Z") (str.to.re "F]7%[j@W%f+")) (str.to.re "")))))
(assert (= (str.to.int x) 0))
(check-sat)
(get-model)
