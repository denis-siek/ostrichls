(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re """""""""ffff") (re.union (str.to.re "YYYYllll%%%%cccc") (str.to.re "111122223333"))))))
(assert (= 20 (str.len x)))
(check-sat)
(get-model)
