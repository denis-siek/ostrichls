(declare-const x String)
(assert (= x "3h!30Z'\t'T'\r'%_%pUD3SN8|FNsWb>D\\[CX(O3};K[9'\x0c'u2Gnhj262'\t'+.Vhz6:eV2;S?ohmEe]'\n'""g#4<b$Z!:-O<A/;*L"))
(assert (str.in.re x (re.* (re.union (str.to.re "@}K.@O|:Ms(BI%qR?#/") (str.to.re "%w%Lg%f%!")))))
(check-sat)
(get-model)
