(declare-const x String)
(assert (= x "bbcccc##%%pp"))
(assert (str.in.re x (re.++ (re.+ (re.+ (str.to.re "cc>>77??"))) (str.to.re ")),,bbccdd"))))
(check-sat)
(get-model)
