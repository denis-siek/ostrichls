(declare-const S String)
(assert (not (str.in.re S (str.to.re "bbb"))))
(assert (str.in.re S (re.++ re.allchar (str.to.re "aaa"))))
(check-sat)
(get-model)
(get-info :reason-unknown)
