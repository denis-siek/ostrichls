(declare-const S String)
(assert (str.in.re S (re.++ (str.to.re "DDDQQQ") re.allchar)))
(assert (not (str.in.re S (re.++ re.allchar (re.++ (str.to.re "QQQ") (re.++ (str.to.re "DDD") re.allchar))))))
(check-sat)
(get-model)
