(declare-const S String)
(assert (str.in.re S (re.++ re.allchar (re.++ (str.to.re "bbbbbb") (re.++ re.allchar (str.to.re "aaaaaa"))))))
(assert (not (str.in.re S (re.++ re.allchar (str.to.re "bbbbbbaaaaaa")))))
(check-sat)
(get-model)
