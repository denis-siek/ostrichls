(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re (str.++ y x) (re.* (str.to.re "'''\x0c'''PN"))))
(check-sat)
(get-model)
