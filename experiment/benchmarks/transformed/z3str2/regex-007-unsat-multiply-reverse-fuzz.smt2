(declare-const x String)
(assert (= (str.len x) 4))
(assert (str.in.re x (re.+ (str.to.re "fl1baTde#"))))
(assert (str.in.re x (re.* (str.to.re "ddr`<l{rCLbbaa"))))
(check-sat)
(get-model)
