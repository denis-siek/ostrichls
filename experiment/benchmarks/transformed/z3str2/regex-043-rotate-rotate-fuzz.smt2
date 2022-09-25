(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.++ (str.to.re "I") (str.to.re "")))))
(assert (= 0 (str.to.int x)))
(assert (not (= x "ab")))
(assert (not (= x "a")))
(assert (not (= x "b")))
(assert (not (= x "U<Ka.")))
(assert (not (= x "#['\t'")))
(assert (not (= x "a")))
(assert (not (= x "a")))
(check-sat)
(get-model)
