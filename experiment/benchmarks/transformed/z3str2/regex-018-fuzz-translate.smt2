(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "1SYS") (str.to.re ")T' '3")))))
(assert (= 4 (str.to.int x)))
(assert (not (= x "12XPC'\n'")))
(check-sat)
(get-model)
