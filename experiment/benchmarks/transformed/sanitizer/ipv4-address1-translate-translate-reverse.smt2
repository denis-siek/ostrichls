(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2"))) (str.to.re "e")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2")))) (str.to.re "e")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2")))) (str.to.re "e")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2"))))))
(assert (not (str.in.re IPAddr (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.union (re.++ (re.range "0" "5") (str.to.re "52")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "2")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (str.to.re "1")))))) (str.to.re "e")) (re.union (re.++ (re.range "0" "5") (str.to.re "52")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "2")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (str.to.re "1"))))))) (str.to.re "e")) (re.union (re.++ (re.range "0" "5") (str.to.re "52")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "2")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (str.to.re "1"))))))) (str.to.re "e")) (re.union (re.++ (re.range "0" "5") (str.to.re "52")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "2")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (str.to.re "1"))))))))))
(check-sat)
