(declare-const x String)
(declare-const y String)
(assert (str.in.re y (re.+ (re.+ (str.to.re "'' ''.?_c<@L#28]")))))
(assert (= (str.len y) 8))
(check-sat)
(get-model)
