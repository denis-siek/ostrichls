(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.* (re.++ (re.range "0" "2") (re.++ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.++ (re.* (re.++ (re.range "0" "2") (re.++ (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.++ (re.* (re.++ (re.range "0" "2") (re.++ (re.* (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9"))) (re.++ (re.range "0" "2") (str.to.re ".."))))) (str.to.re ".."))))) (str.to.re ".."))))))))
(assert (not (str.in.re IPAddr (re.++ (re.range "0" "5") (re.++ (re.union (re.++ (re.++ (re.range "0" "9") (str.to.re "22")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "11")))))) (re.range "0" "4")) (re.union (str.to.re "2255") (re.++ (re.range "0" "5") (re.++ (re.++ (re.union (re.++ (re.++ (re.range "0" "9") (str.to.re "22")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "11")))))) (re.range "0" "4")) (re.union (str.to.re "2255") (re.++ (re.range "0" "5") (re.++ (re.++ (re.union (re.++ (re.++ (re.range "0" "9") (str.to.re "22")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "11")))))) (re.range "0" "4")) (re.union (str.to.re "2255") (re.++ (re.++ (re.range "0" "5") (re.union (re.++ (re.++ (re.range "0" "9") (str.to.re "22")) (re.++ (str.to.re "11") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (re.range "0" "9")))))) (re.range "0" "4"))) (re.union (str.to.re "2255") (str.to.re ".."))))) (str.to.re ".."))))) (str.to.re "..")))))))))
(check-sat)
