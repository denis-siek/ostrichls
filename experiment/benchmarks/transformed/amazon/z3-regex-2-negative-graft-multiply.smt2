(declare-const S String)
(assert (str.in.re S (re.++ (str.to.re "aaaaaabbbbbb") re.allchar)))
(assert (not (str.in.re S (str.to.re "bbbbbb"))))
(check-sat)
(get-model)
