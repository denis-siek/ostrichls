(declare-const IPAddr String)
(assert (>= (str.len IPAddr) 20))
(assert (<= (str.to.int IPAddr) 44))
(assert (str.in.re IPAddr (re.union (re.++ (re.+ (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "SS") (re.union (re.++ (re.* (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "''") (re.++ (re.union (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "..") (re.union (re.* (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.union (re.++ (re.union (str.to.re "2255") (re.range "0" "5")) (re.++ (re.union (str.to.re "") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "00") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "..") (re.union (re.++ (re.++ (str.to.re "2255") (re.range "0" "5")) (re.union (re.union (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.union (str.to.re "00") (str.to.re ""))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "") (re.union (re.++ (re.union (str.to.re "22xx") (re.range "0" "5")) (re.union (re.++ (str.to.re "^^") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "00") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "") (re.union (re.++ (str.to.re "\\\\") (re.range "0" "5")) (re.union (re.union (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "00") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))))))))))))
(check-sat)
