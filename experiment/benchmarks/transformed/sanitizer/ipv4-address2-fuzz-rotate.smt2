(declare-const IPAddr String)
(assert (>= (str.len IPAddr) 10))
(assert (<= (str.to.int IPAddr) 22))
(assert (str.in.re IPAddr (re.union (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.+ (re.++ (re.range "0" "2") (re.++ (re.++ (re.* (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.* (re.++ (re.range "0" "2") (re.++ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.++ (re.* (re.union (re.range "0" "2") (re.++ (re.* (re.++ (re.* (re.+ (re.range "0" "9"))) (re.range "0" "9"))) (re.union (re.range "0" "2") (str.to.re "."))))) (str.to.re "'"))))) (str.to.re "S"))))))))
(assert (not (str.in.re IPAddr (re.union (re.range "0" "5") (re.union (re.++ (re.union (re.++ (re.range "0" "9") (str.to.re "")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "25") (re.++ (re.range "0" "5") (re.union (re.++ (re.union (re.union (re.++ (re.range "0" "9") (str.to.re "2")) (re.union (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "25") (re.union (re.range "0" "5") (re.union (re.union (re.union (re.++ (re.++ (re.range "0" "9") (str.to.re "^")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "2x") (re.union (re.++ (re.range "0" "5") (re.union (re.union (re.++ (re.range "0" "9") (str.to.re "2")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "")))))) (re.range "0" "4"))) (re.union (str.to.re "\\") (str.to.re ""))))) (str.to.re ""))))) (str.to.re ".")))))))))
(check-sat)
