(declare-const x String)
(declare-const y String)
(assert (str.in.re y (re.* (re.* (str.to.re "P&HA")))))
(assert (= (str.len y) 8))
(check-sat)
(get-model)
