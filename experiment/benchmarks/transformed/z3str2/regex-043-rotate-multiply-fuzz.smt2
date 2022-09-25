(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.+ (re.union (str.to.re "aa") (str.to.re "bb")))))
(assert (= 1 (str.to.int x)))
(assert (not (= x "abbb")))
(assert (not (= x "a?%%&]'\x0b'5'\n'NfW")))
(assert (not (= x "lBdbb")))
(assert (not (= x "|PlgjYb")))
(assert (not (= x "^H:o]!aaa")))
(assert (not (= x "baab")))
(assert (not (= x "Maa")))
(check-sat)
(get-model)
