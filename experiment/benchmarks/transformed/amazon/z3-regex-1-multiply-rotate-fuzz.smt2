(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "|)aa+Y=dB3Q2+x&Yn?'\x0b'e'\t'yZHdcbsrOL1$(93") re.allchar))))
(assert (str.in.re S (re.union re.allchar (re.++ (str.to.re "br") (re.++ (str.to.re "|z!jF5aalB") re.allchar)))))
(check-sat)
(get-model)
(get-info :reason-unknown)
