(declare-const IPAddr String)
(assert (>= (str.len IPAddr) 7))
(assert (<= (str.len IPAddr) 15))
(assert (str.in.re IPAddr (re.++ (re.* (re.++ (re.++ (re.++ (str.to.re "%") (re.* (re.++ (re.++ (re.++ (str.to.re "%") (re.* (re.++ (re.++ (re.++ (str.to.re "%") (re.range "0" "2")) (re.* (re.++ (re.range "0" "9") (re.+ (re.+ (re.range "0" "9")))))) (re.range "0" "2")))) (re.++ (re.range "0" "9") (re.+ (re.+ (re.range "0" "9"))))) (re.range "0" "2")))) (re.++ (re.range "0" "9") (re.+ (re.+ (re.range "0" "9"))))) (re.range "0" "2"))) (re.++ (re.range "0" "9") (re.+ (re.+ (re.range "0" "9")))))))
(assert (not (str.in.re IPAddr (re.++ (re.++ (re.union (str.to.re "52") (re.++ (re.++ (str.to.re "%") (re.++ (re.union (str.to.re "52") (re.++ (re.++ (str.to.re "%") (re.++ (re.union (str.to.re "52") (re.++ (re.union (str.to.re "52") (str.to.re "%")) (re.++ (re.union (re.++ (re.++ (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.opt (re.range "0" "9"))) (re.range "0" "9")) (re.++ (str.to.re "2") (re.range "0" "9"))) (re.range "0" "4")) (re.range "0" "5")))) (re.union (re.++ (re.++ (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.opt (re.range "0" "9"))) (re.range "0" "9")) (re.++ (str.to.re "2") (re.range "0" "9"))) (re.range "0" "4")))) (re.range "0" "5"))) (re.union (re.++ (re.++ (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.opt (re.range "0" "9"))) (re.range "0" "9")) (re.++ (str.to.re "2") (re.range "0" "9"))) (re.range "0" "4")))) (re.range "0" "5"))) (re.union (re.++ (re.++ (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.opt (re.range "0" "9"))) (re.range "0" "9")) (re.++ (str.to.re "2") (re.range "0" "9"))) (re.range "0" "4"))) (re.range "0" "5")))))
(check-sat)
