(declare-const IPAddr String)
(assert (>= (str.len IPAddr) 14))
(assert (<= (str.len IPAddr) 30))
(assert (str.in.re IPAddr (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "ee") (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "ee") (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "ee") (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.++ (re.union (re.++ (str.to.re "2255") (re.range "0" "5")) (re.union (re.++ (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (str.to.re "11"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "ee") (re.++ (re.union (re.++ (str.to.re "2255") (re.range "0" "5")) (re.union (re.++ (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (str.to.re "11"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "ee") (re.++ (re.union (re.++ (str.to.re "2255") (re.range "0" "5")) (re.union (re.++ (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (str.to.re "11"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "ee") (re.union (re.++ (str.to.re "2255") (re.range "0" "5")) (re.union (re.++ (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (str.to.re "11"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))))))))))))
(check-sat)
