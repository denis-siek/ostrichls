(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "..'''\t''\t'''iiaattss==aa99ssPP'''\x0b''\x0b'''cc'''\x0c''\x0c'''00##77PPqqJJ44"))))
(assert (str.in.re x (re.* (str.to.re "aakk((ssll''NNZZcc))uu||KKbbccqq[[ddaaaa33SSEEmm'''\r''\r'''BB88iiSS,,11ssOOgg??AA"))))
(assert (> (str.to.int x) 70))
(assert (< (str.len x) 78))
(check-sat)
(get-model)
