(declare-const S String)
(assert (str.in.re S (str.to.re "Ju8b")))
(assert (not (str.in.re S (re.union (re.++ (re.union (str.to.re "bb0:r") re.allchar) (re.++ re.allchar (str.to.re "8aa"))) re.allchar))))
(check-sat)
(get-model)
