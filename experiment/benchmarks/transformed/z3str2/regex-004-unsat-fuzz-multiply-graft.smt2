(declare-const x String)
(assert (= x "bbcccc##%%pp"))
(assert (str.in.re x (re.++ (str.to.re ")),,bbccdd") (re.+ (str.to.re "cc>>77??")))))
(check-sat)
(get-model)
