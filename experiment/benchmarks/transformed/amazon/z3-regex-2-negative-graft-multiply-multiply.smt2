(declare-const S String)
(assert (str.in.re S (re.++ (str.to.re "aaaaaaaaaaaabbbbbbbbbbbb") re.allchar)))
(assert (not (str.in.re S (re.++ (re.++ (str.to.re "bbbbbbbbbbbb") (re.++ (str.to.re "aaaaaaaaaaaa") re.allchar)) re.allchar))))
(check-sat)
(get-model)
