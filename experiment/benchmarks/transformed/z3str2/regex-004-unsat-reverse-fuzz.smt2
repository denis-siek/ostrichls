(declare-const x String)
(assert (= x "e!vDn'\x0b'3{j'\r'h('\x0c'~e"))
(assert (str.in.re x (re.++ (re.+ (str.to.re "dca")) (re.+ (str.to.re "q&")))))
(check-sat)
(get-model)
