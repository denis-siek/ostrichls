(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "b") (re.* (str.to.re ","))))))
(assert (= (str.len x) 3))
(assert (not (= x ",,b")))
(assert (not (= x ",b,")))
(assert (not (= x ",bb")))
(check-sat)
(get-model)
