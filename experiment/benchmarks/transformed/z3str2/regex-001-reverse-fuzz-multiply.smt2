(declare-const x String)
(declare-const y String)
(assert (= x ""))
(assert (str.in.re x (re.+ (str.to.re "ddbb@@oouu"))))
(check-sat)
(get-model)
