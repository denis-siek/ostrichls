(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.union (re.++ (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "") (re.union (re.++ (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.union (str.to.re "d") (re.++ (re.++ (re.+ (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "u") (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.union (re.++ (re.++ (str.to.re "2W") (re.range "0" "5")) (re.++ (re.++ (str.to.re "") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "d") (re.union (re.++ (re.++ (str.to.re "2e") (re.range "0" "5")) (re.++ (re.union (str.to.re "") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "t") (re.++ (re.++ (re.union (str.to.re "5") (re.range "0" "5")) (re.union (re.union (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.union (str.to.re "r") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "d") (re.++ (re.++ (str.to.re "H''\r''") (re.range "0" "5")) (re.union (re.++ (str.to.re "m") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "0") (re.range "0" "9"))) (re.union (re.range "0" "9") (re.opt (str.to.re "1")))))))))))))))
(check-sat)
