(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "hhhQQQ") re.allchar))))
(assert (str.in.re S (re.++ (re.++ (re.++ (str.to.re "hhh") re.allchar) (str.to.re "QQQ")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
