(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "1122ppjjqq"))))
(assert (= (str.to.int x) 18))
(check-sat)
(get-model)
