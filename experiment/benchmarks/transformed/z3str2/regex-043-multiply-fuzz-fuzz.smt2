(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "") (str.to.re "'")))))
(assert (= 4 (str.len x)))
(assert (not (= x "q/Y?")))
(assert (not (= x ":ZN(>bbS{t#&8*[""Gp7C.z'\x0c'Z' ']HH]-Maa")))
(assert (not (= x "{o`7}f3Tha")))
(assert (not (= x "bq}:1U:#p")))
(assert (not (= x "'i}nI*%!}+/H.$'3Paa")))
(assert (not (= x "[lVK^UU]>R]{)6SDWFjN|v[6EejJ&[BTiSD4KUY'KJ'\r'x9'\t'ijq'\x0b'WD-'\x0c'c#D!#};(iD1<<7H""0'\r'ybUIp:GyKDbf'\t'FD7lN`'=$ZHhH''\r'.Un@s%51wB,d#S'\x0b'\\\\{jB4h""N47ThZahCI#fY' 'f!8$' 'w6)X(%S4s1|#5m^Jm''")))
(assert (not (= x "\\pe2a$RZPv[V;HP""J'\t''\n'q3'Qr:)>G:vl'Dc-o[BS\\4'\x0c'LWb_SrRXT{BE;XIf;'\n'ya??`Y3UnKIZ[{,1ea")))
(check-sat)
(get-model)
