(declare-const S String)
(assert (not (str.in.re S (re.++ re.allchar (str.to.re "YYYddd")))))
(assert (str.in.re S (re.++ re.allchar (re.++ (re.++ (str.to.re "ddd") (str.to.re "YYY")) re.allchar))))
(check-sat)
(get-model)
(get-info :reason-unknown)
