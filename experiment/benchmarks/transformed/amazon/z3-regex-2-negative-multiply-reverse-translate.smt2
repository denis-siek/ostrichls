(declare-const S String)
(assert (str.in.re S (re.++ re.allchar (str.to.re "UUUUUUYYYYYY"))))
(assert (not (str.in.re S (re.++ re.allchar (re.++ (str.to.re "UUUUUU") (re.++ re.allchar (str.to.re "YYYYYY")))))))
(check-sat)
(get-model)
