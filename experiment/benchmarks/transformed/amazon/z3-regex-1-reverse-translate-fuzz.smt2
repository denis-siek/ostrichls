(declare-const S String)
(assert (not (str.in.re S (re.++ re.allchar (str.to.re "Yd0=#Y9")))))
(assert (str.in.re S (re.union re.allchar (re.union (str.to.re "YYY") (re.++ re.allchar (str.to.re "Yd"))))))
(check-sat)
(get-model)
(get-info :reason-unknown)
