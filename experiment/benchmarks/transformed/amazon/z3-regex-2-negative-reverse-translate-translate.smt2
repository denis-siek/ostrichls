(declare-const S String)
(assert (str.in.re S (re.++ re.allchar (str.to.re "}}}EEE"))))
(assert (not (str.in.re S (re.++ re.allchar (re.++ (str.to.re "}}}") (re.++ re.allchar (str.to.re "EEE")))))))
(check-sat)
(get-model)
