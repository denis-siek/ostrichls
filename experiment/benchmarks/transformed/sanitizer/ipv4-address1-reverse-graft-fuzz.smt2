(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.union (re.++ (re.++ (re.union (re.union (re.union (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9"))) (re.* (re.range "0" "2"))) (str.to.re ".")) (re.++ (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.+ (re.range "0" "2")))) (str.to.re "{")) (re.++ (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9"))) (re.* (re.range "0" "2")))) (str.to.re "d")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2"))))))
(assert (not (str.in.re IPAddr (re.++ (re.union (re.++ (re.++ (re.union (re.++ (re.++ (re.union (re.range "0" "5") (str.to.re "2")) (re.++ (re.union (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "l")) (re.union (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "k") (str.to.re "\\")))))) (str.to.re "'")) (re.++ (re.union (re.range "0" "5") (str.to.re "52")) (re.union (re.union (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "2")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "") (str.to.re "f"))))))) (str.to.re ".")) (re.union (re.union (re.range "0" "5") (str.to.re "")) (re.++ (re.++ (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "_")) (re.union (re.union (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.++ (str.to.re "J") (str.to.re "1"))))))) (str.to.re "'\x0c'")) (re.++ (re.++ (re.range "0" "5") (str.to.re "N2")) (re.union (re.++ (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "")) (re.++ (re.union (re.opt (str.to.re "")) (re.range "0" "9")) (re.opt (re.union (str.to.re "`") (re.range "0" "9"))))))))))
(check-sat)
