(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.++ (str.to.re "q") (str.to.re "W")))))
(assert (= 0 (str.to.int x)))
(assert (not (= x "=[5")))
(assert (not (= x ":")))
(assert (not (= x "U")))
(assert (not (= x "::")))
(assert (not (= x "Wu5.!.")))
(assert (not (= x "oo")))
(assert (not (= x "sWoC\\y")))
(check-sat)
(get-model)
