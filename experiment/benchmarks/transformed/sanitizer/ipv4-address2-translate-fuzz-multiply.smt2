(declare-const IPAddr String)
(assert (>= (str.to.int IPAddr) 24))
(assert (<= (str.to.int IPAddr) 60))
(assert (str.in.re IPAddr (re.++ (re.union (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "DD") (re.union (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "88") (re.++ (re.++ (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re "HH") (re.union (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.union (re.union (re.union (str.to.re "'''\x0c''\x0c'''KK55") (re.range "0" "5")) (re.union (re.union (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.union (str.to.re "00") (str.to.re "11"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "HH") (re.++ (re.union (re.++ (str.to.re "2255") (re.range "0" "5")) (re.++ (re.++ (str.to.re "22") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.union (str.to.re "") (str.to.re "11"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "") (re.union (re.union (re.++ (str.to.re "22^^''' '' '''") (re.range "0" "5")) (re.++ (re.union (str.to.re "") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "") (str.to.re "jj"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re ">>") (re.++ (re.++ (str.to.re "66") (re.range "0" "5")) (re.++ (re.union (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.union (str.to.re "") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))))))))))))
(check-sat)
