(declare-const S String)
(assert (str.in.re S (re.union (str.to.re "^xC/y'\n'yRI""y@yqLL") re.allchar)))
(assert (not (str.in.re S (re.++ (re.++ (str.to.re "NcJ") (re.++ (str.to.re "RR") re.allchar)) re.allchar))))
(check-sat)
(get-model)
