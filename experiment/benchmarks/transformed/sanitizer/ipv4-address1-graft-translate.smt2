(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "v") (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "v") (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "v") (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.++ (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "v") (re.++ (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "v") (re.++ (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "v") (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (re.range "0" "9") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (str.to.re "2")))))))))))))))
(check-sat)
