(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "77NN") (str.to.re "1122ppjjqq")))))
(assert (= 18 (str.to.int x)))
(check-sat)
(get-model)
