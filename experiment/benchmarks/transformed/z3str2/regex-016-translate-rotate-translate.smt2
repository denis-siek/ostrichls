(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "QrM'\t'") (str.to.re "123")))))
(assert (= 11 (str.len x)))
(assert (not (= x "QrM'\t'123QrM'\t'")))
(assert (not (= x "QrM'\t'QrM'\t'123")))
(check-sat)
(get-model)
