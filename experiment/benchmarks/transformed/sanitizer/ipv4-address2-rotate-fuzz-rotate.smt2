(declare-const IPAddr String)
(assert (>= (str.to.int IPAddr) 11))
(assert (<= (str.len IPAddr) 17))
(assert (str.in.re IPAddr (re.union (re.union (re.+ (re.+ (re.range "0" "9"))) (re.* (re.union (re.union (re.+ (re.* (re.range "0" "9"))) (re.union (re.union (re.+ (re.+ (re.range "0" "9"))) (re.++ (re.range "0" "9") (re.union (re.++ (re.++ (re.* (re.+ (re.range "0" "9"))) (re.+ (re.++ (re.range "0" "2") (str.to.re "")))) (re.range "0" "2")) (re.+ (str.to.re ""))))) (re.++ (re.union (re.range "0" "9") (re.range "0" "2")) (re.* (str.to.re "."))))) (re.++ (re.range "0" "9") (re.range "0" "2"))))) (re.range "0" "9"))))
(assert (not (str.in.re IPAddr (re.union (re.++ (re.union (re.++ (re.opt (re.range "0" "9")) (re.++ (re.opt (re.++ (str.to.re "") (str.to.re "1"))) (re.range "0" "9"))) (re.union (re.range "0" "9") (re.range "0" "4"))) (re.++ (re.union (re.union (re.opt (re.range "0" "9")) (re.++ (re.opt (re.++ (str.to.re "2") (str.to.re "'"))) (re.range "0" "9"))) (re.union (re.range "0" "9") (re.range "0" "4"))) (re.++ (re.union (re.++ (re.union (re.union (re.union (re.opt (re.range "0" "9")) (re.union (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.range "0" "9"))) (re.union (re.range "0" "9") (re.range "0" "4"))) (re.++ (re.++ (re.union (re.++ (re.++ (re.++ (re.union (re.union (re.opt (re.range "0" "9")) (re.++ (re.opt (re.union (str.to.re "") (str.to.re ""))) (re.range "0" "9"))) (re.++ (re.range "0" "9") (re.range "0" "4"))) (re.range "0" "5")) (re.++ (str.to.re "1X?)") (str.to.re "."))) (re.union (str.to.re "Y") (str.to.re "e`"))) (re.union (str.to.re "") (str.to.re "."))) (re.range "0" "5")) (str.to.re "95"))) (re.union (str.to.re "?") (str.to.re ""))) (re.range "0" "5")) (str.to.re "")))) (re.++ (str.to.re "2") (re.range "0" "5"))))))
(check-sat)
