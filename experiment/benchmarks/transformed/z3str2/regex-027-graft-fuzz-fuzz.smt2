(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "") (re.* (str.to.re "N"))))))
(assert (= 6 (str.to.int x)))
(assert (not (= x "")))
(assert (not (= x "a")))
(assert (not (= x ".")))
(check-sat)
(get-model)
