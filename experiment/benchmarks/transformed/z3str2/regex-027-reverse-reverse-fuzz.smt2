(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.* (str.to.re "Z")) (str.to.re "")))))
(assert (= (str.to.int x) 0))
(assert (not (= x "u")))
(assert (not (= x "a")))
(assert (not (= x "8A0ab")))
(check-sat)
(get-model)
