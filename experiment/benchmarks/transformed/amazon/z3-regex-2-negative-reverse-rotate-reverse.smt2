(declare-const S String)
(assert (str.in.re S (re.++ (str.to.re "aaabbb") re.allchar)))
(assert (not (str.in.re S (re.++ (re.++ re.allchar (re.++ (str.to.re "bbb") (str.to.re "aaa"))) re.allchar))))
(check-sat)
(get-model)
