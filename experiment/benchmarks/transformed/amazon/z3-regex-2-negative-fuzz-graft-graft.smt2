(declare-const S String)
(assert (str.in.re S (str.to.re "b8uJ")))
(assert (not (str.in.re S (re.union (str.to.re "aa8") re.allchar))))
(check-sat)
(get-model)
