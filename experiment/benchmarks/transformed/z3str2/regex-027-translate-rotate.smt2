(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "<")) (str.to.re "a")))))
(assert (= (str.len x) 3))
(assert (not (= x "aa<")))
(assert (not (= x "a<<")))
(assert (not (= x "<a<")))
(check-sat)
(get-model)
