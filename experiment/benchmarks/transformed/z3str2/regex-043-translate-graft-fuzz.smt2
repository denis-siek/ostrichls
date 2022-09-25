(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.+ (str.to.re "]"))))
(assert (= (str.to.int x) 4))
(assert (not (= x ")|")))
(assert (not (= x "+]")))
(assert (not (= x "f+")))
(assert (not (= x "")))
(assert (not (= x "l_r+n")))
(assert (not (= x "8+)")))
(assert (not (= x "++")))
(check-sat)
(get-model)
