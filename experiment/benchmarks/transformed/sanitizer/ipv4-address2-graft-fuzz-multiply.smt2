(declare-const IPAddr String)
(assert (>= (str.to.int IPAddr) 6))
(assert (<= 50 (str.len IPAddr)))
(assert (str.in.re IPAddr (re.++ (re.++ (re.+ (re.range "0" "2")) (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "qq") (re.++ (re.union (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "") (re.++ (re.++ (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "..") (re.++ (re.* (re.range "0" "2")) (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.++ (re.union (re.++ (str.to.re "{{::") (re.range "0" "5")) (re.union (re.union (str.to.re "__") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "") (str.to.re "VV"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "..") (re.++ (re.++ (re.union (str.to.re "22ZZ") (re.range "0" "5")) (re.union (re.union (str.to.re "%%") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.union (str.to.re "yy") (str.to.re ""))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "..") (re.++ (re.++ (re.union (str.to.re "44||") (re.range "0" "5")) (re.++ (re.++ (str.to.re "55") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "##") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "33") (re.union (re.++ (str.to.re "{{EE") (re.range "0" "5")) (re.++ (re.union (str.to.re "TT") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (re.union (re.range "0" "9") (re.opt (re.range "0" "9"))))) (str.to.re "11")))))))))))))
(check-sat)
