(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "aaKK::^^GG''''' '' '''''II77QQjj..LL++9966") re.allchar))))
(assert (str.in.re S (re.union re.allchar (re.++ (str.to.re "``bb}}TT..") (re.union (str.to.re "aa11") re.allchar)))))
(check-sat)
(get-model)
(get-info :reason-unknown)
