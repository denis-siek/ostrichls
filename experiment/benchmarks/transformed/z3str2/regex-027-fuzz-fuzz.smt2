(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.+ (str.to.re "^")) (str.to.re "")))))
(assert (= (str.len x) 0))
(assert (not (= x "'\t''\x0b'5T")))
(assert (not (= x "UA6ZI.'\x0b'B'\x0b'i:dFxsb.5+5e6")))
(assert (not (= x "u-M'\x0b'@WkMi')E8F""a'5X6fD'\x0b'bppv/'NxL!Fs_$P")))
(check-sat)
(get-model)
