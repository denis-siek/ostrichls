(declare-const x String)
(declare-const y String)
(assert (= x "-[aA+3ypAVC-S'\n'RgIaqJu~3' 'FTD/a"))
(assert (str.in.re x (re.* (re.* (str.to.re "deA")))))
(check-sat)
(get-model)
