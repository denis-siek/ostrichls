(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re ".''\t''iats=a9sP''\x0b''c''\x0c''0#7PqJ4"))))
(assert (str.in.re x (str.to.re "ak(sl'NZc)u|Kbcq[daa3SEm''\r''B8iS,1sOg?A")))
(assert (> (str.to.int x) 35))
(assert (< 39 (str.len x)))
(check-sat)
(get-model)
