(declare-const S String)
(assert (not (str.in.re S (re.++ re.allchar (str.to.re "bbbbbbaaaaaa")))))
(assert (str.in.re S (re.++ (re.++ (re.++ re.allchar (str.to.re "aaaaaa")) (str.to.re "bbbbbb")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
