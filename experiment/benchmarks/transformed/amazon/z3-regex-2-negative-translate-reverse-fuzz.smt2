(declare-const S String)
(assert (str.in.re S (re.union re.allchar (str.to.re "$kJge>>oy7D.C2gTSG^k['Bu<iAmcJ+T`$-y'~pXUfVyO'\x0b'R&Uo9}vzxl]'\t'hLtzQhqh1/m*a#=?K1;a)|'\t''\r'''"))))
(assert (not (str.in.re S (re.union re.allchar (re.++ (str.to.re "'\x0b'") (re.++ re.allchar (str.to.re "''&_&z\\_6T'-?r0'\x0c'vw>4a''rrt[#'\r'(eI0")))))))
(check-sat)
(get-model)
