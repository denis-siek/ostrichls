(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.union (str.to.re "Z") (str.to.re "tot")))))
(assert (= 3 (str.len x)))
(assert (not (= x "Ztottot")))
(assert (not (= x "ZtotZ")))
(assert (not (= x "tottotZ")))
(assert (not (= x "tottottot")))
(assert (not (= x "totZZ")))
(assert (not (= x "totZtot")))
(assert (not (= x "ZZZ")))
(check-sat)
(get-model)
