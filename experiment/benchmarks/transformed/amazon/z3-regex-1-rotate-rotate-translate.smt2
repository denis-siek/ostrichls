(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "---===") re.allchar))))
(assert (str.in.re S (re.++ (str.to.re "---") (re.++ (re.++ re.allchar (str.to.re "===")) re.allchar))))
(check-sat)
(get-model)
(get-info :reason-unknown)
