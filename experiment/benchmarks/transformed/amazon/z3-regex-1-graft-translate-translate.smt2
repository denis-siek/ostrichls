(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "!!!xxx") re.allchar))))
(assert (str.in.re S (re.++ (re.++ (str.to.re "xxx") (re.++ (str.to.re "!!!") re.allchar)) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
