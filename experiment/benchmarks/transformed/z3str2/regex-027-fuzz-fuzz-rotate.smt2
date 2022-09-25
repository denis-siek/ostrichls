(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.+ (str.to.re "")) (str.to.re "C")))))
(assert (= (str.to.int x) 1))
(assert (not (= x "|")))
(assert (not (= x "wO")))
(assert (not (= x "?\\9E''\x0c''SD*2")))
(check-sat)
(get-model)
