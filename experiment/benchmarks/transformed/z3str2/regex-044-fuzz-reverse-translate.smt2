(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.range "0" "9"))))
(assert (= 1 (str.to.int x)))
(assert (not (= x "")))
(assert (not (= x "0")))
(assert (not (= x "3")))
(assert (not (= x "J")))
(assert (not (= x "")))
(assert (not (= x "6")))
(assert (not (= x "T")))
(assert (not (= x "%")))
(assert (not (= x "'\n'")))
(check-sat)
(get-model)
