(declare-const IPAddr String)
(assert (>= (str.to.int IPAddr) 5))
(assert (<= (str.to.int IPAddr) 12))
(assert (str.in.re IPAddr (re.union (re.++ (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.+ (re.union (re.range "0" "2") (re.++ (re.union (re.* (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.+ (re.++ (re.range "0" "2") (re.union (re.union (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.++ (re.+ (re.++ (re.range "0" "2") (re.union (re.* (re.++ (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9"))) (re.++ (re.range "0" "2") (str.to.re "e"))))) (str.to.re ""))))) (str.to.re "x"))))))))
(assert (not (str.in.re IPAddr (re.++ (re.range "0" "5") (re.++ (re.union (re.union (re.union (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "^") (re.union (re.range "0" "5") (re.++ (re.++ (re.++ (re.++ (re.++ (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "\\") (str.to.re "1")))))) (re.range "0" "4")) (re.++ (str.to.re "m") (re.union (re.range "0" "5") (re.++ (re.union (re.++ (re.++ (re.union (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re ".y") (re.union (re.++ (re.range "0" "5") (re.++ (re.union (re.union (re.range "0" "9") (str.to.re "X")) (re.union (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "^") (str.to.re "")))))) (re.range "0" "4"))) (re.union (str.to.re "") (str.to.re "d"))))) (str.to.re ""))))) (str.to.re ".")))))))))
(check-sat)
