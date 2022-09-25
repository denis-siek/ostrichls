(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.range "0" "9"))))
(assert (= 8 (str.len x)))
(assert (not (= x "11111111")))
(assert (not (= x "00000000")))
(assert (not (= x "33333333")))
(assert (not (= x "22222222")))
(assert (not (= x "88888888")))
(assert (not (= x "66666666")))
(assert (not (= x "44444444")))
(assert (not (= x "99999999")))
(assert (not (= x "77777777")))
(check-sat)
(get-model)
