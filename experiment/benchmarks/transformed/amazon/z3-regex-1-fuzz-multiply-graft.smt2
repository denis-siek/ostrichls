(declare-const S String)
(assert (not (str.in.re S (re.++ (re.++ (str.to.re "aa11") re.allchar) re.allchar))))
(assert (str.in.re S (re.union (re.union (str.to.re "aaKK::^^GG'''' '''' ''''II77QQjj..LL++9966") (str.to.re "``bb}}TT..")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
