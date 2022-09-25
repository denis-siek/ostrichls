(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.union (str.to.re "FF") (str.to.re "''")))))
(assert (= 6 (str.len x)))
(assert (not (= x "FF''''")))
(assert (not (= x "FF''FF")))
(assert (not (= x "''''FF")))
(assert (not (= x "''''''")))
(assert (not (= x "''FFFF")))
(assert (not (= x "''FF''")))
(assert (not (= x "FFFFFF")))
(check-sat)
(get-model)
