(declare-const x String)
(assert (= (str.len x) 8))
(assert (str.in.re x (re.* (str.to.re "%nM"))))
(assert (str.in.re x (re.* (str.to.re "' 'b%M"))))
(check-sat)
(get-model)
