(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "b") (str.to.re "32|=")))))
(assert (= 19 (str.len x)))
(assert (not (= x "6mxLvcW[*br)\\2Dfm92BeLda")))
(assert (not (= x "2x>*bX'\x0b'Kh)dcba")))
(check-sat)
(get-model)
