(declare-const S String)
(assert (not (str.in.re S (re.++ re.allchar (str.to.re "~~~%%%")))))
(assert (str.in.re S (re.++ (re.++ (re.++ re.allchar (str.to.re "%%%")) (str.to.re "~~~")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
