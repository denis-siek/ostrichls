(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2"))) (str.to.re "..")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2")))) (str.to.re "..")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2")))) (str.to.re "..")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2"))))))
(assert (not (str.in.re IPAddr (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.union (re.++ (re.range "0" "5") (str.to.re "5522")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "22")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "11")))))) (str.to.re "..")) (re.union (re.++ (re.range "0" "5") (str.to.re "5522")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "22")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "11"))))))) (str.to.re "..")) (re.union (re.++ (re.range "0" "5") (str.to.re "5522")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "22")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "11"))))))) (str.to.re "..")) (re.union (re.++ (re.range "0" "5") (str.to.re "5522")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "22")) (re.++ (re.++ (re.opt (re.range "0" "9")) (str.to.re "11")) (re.opt (re.union (str.to.re "00") (re.range "0" "9"))))))))))
(check-sat)
