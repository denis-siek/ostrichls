(declare-const S String)
(assert (str.in.re S (re.++ (str.to.re "'\n']p6/_bk") re.allchar)))
(assert (not (str.in.re S (re.union (re.union (re.union (str.to.re "'\n''\n'") re.allchar) (str.to.re "kk")) re.allchar))))
(check-sat)
(get-model)
