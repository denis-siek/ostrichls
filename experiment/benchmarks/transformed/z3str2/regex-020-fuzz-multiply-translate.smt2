(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (re.+ (str.to.re "")) (str.to.re "")))))
(assert (= (str.to.int x) 12))
(assert (not (= x "~~~~")))
(assert (not (= x "XX<<kk||ZZ==&&jj")))
(assert (not (= x "//WW??")))
(check-sat)
(get-model)
