(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.* (re.++ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.++ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.++ (re.range "0" "9") (re.++ (re.++ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.* (re.++ (re.range "0" "2") (str.to.re ".")))) (re.range "0" "2")) (re.* (str.to.re "."))))) (re.++ (re.++ (re.range "0" "9") (re.range "0" "2")) (re.* (str.to.re "."))))) (re.++ (re.range "0" "9") (re.range "0" "2"))))) (re.range "0" "9"))))
(assert (not (str.in.re IPAddr (re.++ (re.union (re.++ (re.++ (re.opt (re.range "0" "9")) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.range "0" "9"))) (re.++ (re.range "0" "9") (re.range "0" "4"))) (re.union (re.++ (re.++ (re.opt (re.range "0" "9")) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.range "0" "9"))) (re.++ (re.range "0" "9") (re.range "0" "4"))) (re.++ (re.++ (re.union (re.union (re.++ (re.++ (re.opt (re.range "0" "9")) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.range "0" "9"))) (re.++ (re.range "0" "9") (re.range "0" "4"))) (re.++ (re.++ (re.union (re.union (re.++ (re.union (re.++ (re.++ (re.opt (re.range "0" "9")) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.range "0" "9"))) (re.++ (re.range "0" "9") (re.range "0" "4"))) (re.range "0" "5")) (str.to.re "2")) (re.++ (str.to.re "2") (str.to.re "25"))) (re.++ (str.to.re "2") (str.to.re "."))) (re.range "0" "5")) (str.to.re "25"))) (re.++ (str.to.re "2") (str.to.re "."))) (re.range "0" "5")) (str.to.re "25")))) (re.++ (re.union (str.to.re "25") (str.to.re ".")) (re.range "0" "5"))))))
(check-sat)
