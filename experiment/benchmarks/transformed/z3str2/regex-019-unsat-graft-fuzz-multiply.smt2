(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "")))
(assert (= (str.to.int x) 6))
(assert (not (= x "[[..,,jjmm++{{..")))
(check-sat)
(get-model)
