(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "22**VV'''''\r''\r'''''") (str.to.re "BBAA")))))
(assert (= 16 (str.to.int x)))
(assert (not (= x "BBNNqqSSvvCCzz'''''\t''\t'''''9911")))
(check-sat)
(get-model)
