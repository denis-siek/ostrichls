(declare-const x String)
(declare-const y String)
(assert (= x "aaa' 'D8&n3{O'\x0b''D3' 'hQJ|`<jXqdjl'\x0b'"))
(assert (str.in.re x (str.to.re "ed")))
(check-sat)
(get-model)
