(declare-const x String)
(declare-const y String)
(assert (= x "MdYhJ#(toyBN`MMMM'\x0b':rMkvkRmk<5' 'e1n4MyhMk,kq'\r'IAx{7[n'\r'yyk,kB\\0'\r'aykckzM"))
(assert (str.in.re x (re.* (re.* (str.to.re "'\n'['\x0b'y=")))))
(check-sat)
(get-model)
