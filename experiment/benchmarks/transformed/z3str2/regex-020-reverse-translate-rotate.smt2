(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "-") (re.* (str.to.re "w"))))))
(assert (= (str.len x) 3))
(assert (not (= x "ww-")))
(assert (not (= x "w-w")))
(assert (not (= x "w--")))
(check-sat)
(get-model)
