(declare-const IPAddr String)
(assert (>= (str.to.int IPAddr) 13))
(assert (<= (str.len IPAddr) 26))
(assert (str.in.re IPAddr (re.++ (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "v") (re.++ (re.union (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.union (str.to.re "8") (re.++ (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "") (re.++ (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.++ (re.union (re.++ (str.to.re "%R'\n'K5") (re.range "0" "5")) (re.++ (re.union (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "0") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "=") (re.union (re.union (re.union (str.to.re "'\t'(") (re.range "0" "5")) (re.union (re.union (str.to.re "") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "") (str.to.re "e"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "") (re.++ (re.++ (re.union (str.to.re "rY.S''\n'") (re.range "0" "5")) (re.union (re.union (str.to.re "") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "") (str.to.re "3"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re ">") (re.union (re.++ (str.to.re "g") (re.range "0" "5")) (re.union (re.++ (str.to.re "t") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "") (str.to.re ""))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))))))))))))
(check-sat)
