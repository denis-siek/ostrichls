(declare-const S String)
(assert (not (str.in.re S (re.++ re.allchar (str.to.re "bbbaaa")))))
(assert (str.in.re S (re.++ (re.++ (re.++ re.allchar (str.to.re "aaa")) (str.to.re "bbb")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
