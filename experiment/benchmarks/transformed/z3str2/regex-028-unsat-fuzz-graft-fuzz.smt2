(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.+ (str.to.re "Qx' '~'\x0b'`z19' 'np.O(4:2'=''*,3'''q#@+")))))
(assert (str.in.re x (re.+ (str.to.re "[/abP"))))
(assert (str.in.re x (str.to.re "a")))
(assert (> 1 (str.to.int x)))
(check-sat)
(get-model)
