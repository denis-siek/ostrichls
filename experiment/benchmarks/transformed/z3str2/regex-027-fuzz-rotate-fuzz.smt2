(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.+ (str.to.re "")) (str.to.re "")))))
(assert (= (str.to.int x) 9))
(assert (not (= x "ew")))
(assert (not (= x "wb")))
(assert (not (= x "'\r't`YR""B")))
(check-sat)
(get-model)
