(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.range "0" "9") (re.* (re.range "0" "2"))) (re.+ (re.++ (re.++ (str.to.re "d") (re.++ (re.+ (re.++ (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.++ (re.range "0" "9") (re.* (re.range "0" "2"))))) (re.++ (re.range "0" "9") (str.to.re "d"))) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.++ (re.range "0" "9") (re.* (re.range "0" "2"))))))) (str.to.re "d"))) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.++ (re.range "0" "9") (re.* (re.range "0" "2"))))))))))
(assert (not (str.in.re IPAddr (re.++ (re.++ (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "9") (re.++ (re.++ (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "1")))) (re.opt (re.range "0" "9"))))) (re.++ (re.++ (re.union (re.range "0" "5") (str.to.re "d")) (re.++ (re.++ (re.union (re.++ (str.to.re "52") (re.union (re.range "0" "4") (re.++ (str.to.re "2") (re.++ (re.range "0" "9") (re.++ (re.++ (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "1")))) (re.opt (re.range "0" "9"))))))) (re.range "0" "5")) (re.++ (str.to.re "52") (str.to.re "d"))) (re.union (re.++ (str.to.re "52") (re.union (re.range "0" "4") (re.++ (str.to.re "2") (re.++ (re.range "0" "9") (re.++ (re.++ (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "1")))) (re.opt (re.range "0" "9"))))))) (re.range "0" "5")))) (str.to.re "d"))) (re.union (re.++ (str.to.re "52") (re.union (re.range "0" "4") (re.++ (str.to.re "2") (re.++ (re.range "0" "9") (re.++ (re.++ (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "1")))) (re.opt (re.range "0" "9"))))))) (re.range "0" "5"))) (re.range "0" "4")))))
(check-sat)
