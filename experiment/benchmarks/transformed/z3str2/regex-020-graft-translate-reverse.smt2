(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "?")) (str.to.re "U")))))
(assert (= 3 (str.len x)))
(assert (not (= x "UU?")))
(assert (not (= x "U?U")))
(assert (not (= x "U??")))
(check-sat)
(get-model)
