(declare-const S String)
(assert (not (str.in.re S (re.union re.allchar (str.to.re "b*DD\\&+GDh[!w]t9R'\x0b'M~~Eaadw6#s")))))
(assert (str.in.re S (re.++ re.allchar (re.union (str.to.re "bbSIQb") (re.union re.allchar (str.to.re "&aa"))))))
(check-sat)
(get-model)
(get-info :reason-unknown)
