(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "ssY@Y") re.allchar))))
(assert (str.in.re S (re.union (re.++ (re.++ (str.to.re "sAE") re.allchar) (str.to.re "\\oY")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
