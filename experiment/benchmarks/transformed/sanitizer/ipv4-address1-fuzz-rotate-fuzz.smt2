(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.union (re.union (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.+ (re.++ (re.range "0" "2") (re.union (re.++ (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.+ (re.++ (re.range "0" "2") (re.union (re.++ (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.* (re.union (re.range "0" "2") (re.++ (re.+ (re.union (re.* (re.* (re.range "0" "9"))) (re.range "0" "9"))) (re.union (re.range "0" "2") (str.to.re "u"))))) (str.to.re ""))))) (str.to.re "."))))))))
(assert (not (str.in.re IPAddr (re.++ (re.range "0" "5") (re.++ (re.++ (re.union (re.union (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "=") (str.to.re "")))))) (re.range "0" "4")) (re.union (str.to.re "K<j#66['Z$J)@'\n'F'<0{G") (re.++ (re.range "0" "5") (re.++ (re.union (re.++ (re.++ (re.union (re.range "0" "9") (str.to.re "'\n'")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "?") (str.to.re "S")))))) (re.range "0" "4")) (re.++ (str.to.re "x") (re.union (re.range "0" "5") (re.union (re.union (re.union (re.++ (re.++ (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "#") (re.++ (re.++ (re.range "0" "5") (re.++ (re.++ (re.++ (re.range "0" "9") (str.to.re "")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "'\t'")))))) (re.range "0" "4"))) (re.++ (str.to.re "XJ") (str.to.re ""))))) (str.to.re ""))))) (str.to.re "\\")))))))))
(check-sat)
