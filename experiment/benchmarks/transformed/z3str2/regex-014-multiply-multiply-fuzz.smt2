(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "#crqQ71Vh'\t'[g'y'9_27b"))))
(assert (str.in.re y (re.* (str.to.re "a3V?jiSa""ab8B"))))
(assert (= (str.len x) 2))
(assert (= (str.len y) 5))
(check-sat)
(get-model)
