(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "&&&qqq") re.allchar))))
(assert (str.in.re S (re.++ re.allchar (re.++ (str.to.re "qqq") (re.++ (str.to.re "&&&") re.allchar)))))
(check-sat)
(get-model)
(get-info :reason-unknown)
