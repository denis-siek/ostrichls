(declare-const x String)
(assert (= x "dc?^]"))
(assert (str.in.re x (re.++ (re.+ (re.+ (str.to.re "de"))) (str.to.re "c"))))
(check-sat)
(get-model)
