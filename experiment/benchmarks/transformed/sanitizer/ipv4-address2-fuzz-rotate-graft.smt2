(declare-const IPAddr String)
(assert (>= (str.len IPAddr) 7))
(assert (<= 27 (str.to.int IPAddr)))
(assert (str.in.re IPAddr (re.++ (re.++ (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.+ (re.++ (re.range "0" "2") (re.union (re.++ (re.* (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.* (re.union (re.range "0" "2") (re.union (re.union (re.* (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.++ (re.* (re.++ (re.range "0" "2") (re.union (re.+ (re.++ (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9"))) (re.++ (re.range "0" "2") (str.to.re "5"))))) (str.to.re ""))))) (str.to.re "x"))))))))
(assert (not (str.in.re IPAddr (re.++ (re.range "0" "5") (re.++ (re.++ (re.union (re.++ (re.range "0" "9") (str.to.re "2")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "^?") (re.++ (re.range "0" "5") (re.++ (re.++ (re.union (re.++ (re.union (re.range "0" "9") (str.to.re ":")) (re.union (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "\\") (str.to.re "1")))))) (re.range "0" "4")) (re.union (str.to.re "m") (re.union (re.range "0" "5") (re.union (re.union (re.++ (re.union (re.union (re.range "0" "9") (str.to.re "2")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "25") (re.union (re.union (re.range "0" "5") (re.++ (re.++ (re.++ (re.range "0" "9") (str.to.re "X")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "(") (str.to.re "")))))) (re.range "0" "4"))) (str.to.re "x")))) (str.to.re "."))))) (str.to.re ".")))))))))
(check-sat)
