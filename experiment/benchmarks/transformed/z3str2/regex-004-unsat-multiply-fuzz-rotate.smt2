(declare-const x String)
(assert (= x "SHxe*Xr*+G(abxtI.cc`+`cL[Tf1F&.Ia}a:"))
(assert (str.in.re x (re.++ (re.* (re.* (str.to.re "Q~&*ON'' ''dT{Cqe"))) (str.to.re "aabc$V31"))))
(check-sat)
(get-model)
