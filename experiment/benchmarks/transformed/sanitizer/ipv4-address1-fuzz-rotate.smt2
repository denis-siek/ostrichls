(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.* (re.++ (re.range "0" "2") (re.++ (re.union (re.* (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.++ (re.* (re.++ (re.range "0" "2") (re.union (re.++ (re.* (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.* (re.++ (re.range "0" "2") (re.++ (re.+ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9"))) (re.union (re.range "0" "2") (str.to.re ""))))) (str.to.re "1"))))) (str.to.re ""))))))))
(assert (not (str.in.re IPAddr (re.union (re.range "0" "5") (re.union (re.++ (re.union (re.union (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "") (str.to.re "1")))))) (re.range "0" "4")) (re.union (str.to.re "5") (re.union (re.range "0" "5") (re.++ (re.union (re.++ (re.++ (re.union (re.range "0" "9") (str.to.re "2")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "1")))))) (re.range "0" "4")) (re.++ (str.to.re "?1") (re.++ (re.range "0" "5") (re.++ (re.++ (re.++ (re.union (re.union (re.range "0" "9") (str.to.re "m")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "c") (str.to.re "1")))))) (re.range "0" "4")) (re.union (str.to.re ".dA") (re.++ (re.union (re.range "0" "5") (re.++ (re.++ (re.++ (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "") (str.to.re "<")))))) (re.range "0" "4"))) (re.union (str.to.re "") (str.to.re ""))))) (str.to.re "."))))) (str.to.re ".")))))))))
(check-sat)
