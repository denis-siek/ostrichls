(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.* (str.to.re "")) (str.to.re "")))))
(assert (= (str.to.int x) 4))
(assert (not (= x "b")))
(assert (not (= x "wa")))
(assert (not (= x "")))
(check-sat)
(get-model)
