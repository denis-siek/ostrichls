(declare-const x String)
(declare-const y String)
(assert (= x "u%0''''"))
(assert (str.in.re x (re.+ (str.to.re "m7]83"))))
(check-sat)
(get-model)
