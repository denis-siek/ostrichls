(declare-const S String)
(assert (str.in.re S (re.++ re.allchar (str.to.re "bbbaaa"))))
(assert (not (str.in.re S (re.++ re.allchar (re.++ (str.to.re "bbb") (re.++ re.allchar (str.to.re "aaa")))))))
(check-sat)
(get-model)
