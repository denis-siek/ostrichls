(declare-const IPAddr String)
(assert (>= (str.to.int IPAddr) 3))
(assert (<= (str.to.int IPAddr) 17))
(assert (str.in.re IPAddr (re.++ (re.++ (re.range "0" "9") (re.* (re.range "0" "2"))) (re.* (re.++ (re.union (str.to.re "") (re.++ (re.+ (re.union (re.union (re.++ (re.* (re.range "0" "9")) (re.* (re.++ (re.range "0" "9") (re.* (re.range "0" "2"))))) (re.++ (re.range "0" "9") (str.to.re "."))) (re.++ (re.* (re.range "0" "9")) (re.* (re.++ (re.range "0" "9") (re.* (re.range "0" "2"))))))) (str.to.re "."))) (re.++ (re.* (re.range "0" "9")) (re.+ (re.union (re.range "0" "9") (re.* (re.range "0" "2"))))))))))
(assert (not (str.in.re IPAddr (re.union (re.++ (re.++ (re.union (str.to.re "") (re.union (re.range "0" "9") (re.union (re.union (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "")))) (re.opt (re.range "0" "9"))))) (re.union (re.++ (re.union (re.range "0" "5") (str.to.re ".")) (re.++ (re.++ (re.union (re.union (str.to.re "52") (re.union (re.range "0" "4") (re.++ (str.to.re "") (re.++ (re.range "0" "9") (re.++ (re.union (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "J")))) (re.opt (re.range "0" "9"))))))) (re.range "0" "5")) (re.++ (str.to.re "/O") (str.to.re "W"))) (re.union (re.union (str.to.re "") (re.union (re.range "0" "4") (re.union (str.to.re "2") (re.union (re.range "0" "9") (re.union (re.union (re.range "0" "9") (re.opt (re.++ (str.to.re "''\r''") (str.to.re "6")))) (re.opt (re.range "0" "9"))))))) (re.range "0" "5")))) (str.to.re ""))) (re.++ (re.++ (str.to.re ">''\n''S") (re.union (re.range "0" "4") (re.++ (str.to.re "") (re.++ (re.range "0" "9") (re.union (re.++ (re.range "0" "9") (re.opt (re.++ (str.to.re "") (str.to.re "1")))) (re.opt (re.range "0" "9"))))))) (re.range "0" "5"))) (re.range "0" "4")))))
(check-sat)
