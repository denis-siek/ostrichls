(declare-const IPAddr String)
(assert (>= (str.len IPAddr) 7))
(assert (<= 7 (str.to.int IPAddr)))
(assert (str.in.re IPAddr (re.++ (re.union (re.union (re.++ (re.++ (re.++ (re.union (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9"))) (re.* (re.range "0" "2"))) (str.to.re ".")) (re.++ (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.+ (re.range "0" "2")))) (str.to.re "^")) (re.union (re.++ (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))) (re.* (re.range "0" "2")))) (str.to.re "")) (re.union (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))) (re.* (re.range "0" "2"))))))
(assert (not (str.in.re IPAddr (re.++ (re.++ (re.union (re.++ (re.union (re.++ (re.++ (re.union (re.range "0" "5") (str.to.re "j4i")) (re.++ (re.union (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "n")) (re.++ (str.to.re "1") (re.opt (re.++ (str.to.re "D") (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9"))))))) (str.to.re "")) (re.++ (re.union (re.range "0" "5") (str.to.re "5^2")) (re.++ (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "^")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.++ (str.to.re ".") (str.to.re ""))))))) (str.to.re ".")) (re.++ (re.union (re.range "0" "5") (str.to.re "]")) (re.union (re.union (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "f")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re ""))))))) (str.to.re "M")) (re.union (re.union (re.range "0" "5") (str.to.re "(.2")) (re.union (re.union (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "!")) (re.++ (re.union (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "k") (str.to.re "1"))))))))))
(check-sat)
