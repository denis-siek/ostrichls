(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re ""))))
(assert (= 3 (str.len x)))
(assert (not (= x "Z1@LvhD9/")))
(check-sat)
(get-model)
