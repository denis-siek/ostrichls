(declare-const S String)
(assert (not (str.in.re S (re.++ re.allchar (str.to.re "6699++LL..jjQQ77II'''' '''' ''''GG^^::KKaa")))))
(assert (str.in.re S (re.union (re.union (re.++ re.allchar (str.to.re "11aa")) (str.to.re "..TT}}bb``")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
