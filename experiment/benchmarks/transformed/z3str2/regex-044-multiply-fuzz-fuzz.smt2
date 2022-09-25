(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.range "0" "9"))))
(assert (= 0 (str.to.int x)))
(assert (not (= x "1")))
(assert (not (= x "0")))
(assert (not (= x "LV")))
(assert (not (= x "")))
(assert (not (= x "J")))
(assert (not (= x "jvl=2*")))
(assert (not (= x "Ym\\J")))
(assert (not (= x "g+")))
(assert (not (= x "7")))
(check-sat)
(get-model)
