(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "U2bMP,t'\x0c'L5'\x0c'LL"))))
(assert (str.in.re x (re.+ (str.to.re "==' '+ZlQV'\x0c'o'\x0c'<p'\x0c'A'\x0c'vu:ppq4'\x0c''\t''\x0c'..Vbi'\x0c'5.@'\x0c'eg\\twOOB' 'HE~2iGdl&'\x0c'A'\x0c'F0zOcODXb$KW[Ce69$'\n'Xv3Yvj}x7:sL7p^b4$'\x0b'h^&b}SsfSvO3J'=J*){K5TcI&Q5,pv""^D'\x0c';'\x0c'A'\x0c'J/|zj'\x0c''\t''\x0c';+Zu+dbER#YE&pG0'\x0c'o'\x0c''\n'"))))
(assert (> (str.to.int x) 11))
(assert (< (str.len x) 9))
(check-sat)
(get-model)
