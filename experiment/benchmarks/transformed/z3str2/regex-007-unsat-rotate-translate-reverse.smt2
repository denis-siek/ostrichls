(declare-const x String)
(assert (= (str.len x) 8))
(assert (str.in.re x (re.* (str.to.re "Mn%"))))
(assert (str.in.re x (re.* (str.to.re "M%b'' ''"))))
(check-sat)
(get-model)
