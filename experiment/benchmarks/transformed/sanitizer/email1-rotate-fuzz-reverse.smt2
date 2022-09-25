(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.to.int Username) 98))
(assert (> (str.to.int Username) 0))
(assert (<= (str.to.int Domainname) 424))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ (str.++ Username Domainname) "")))
(assert (str.in.re Email (re.++ (re.union (re.++ (re.range "a" "z") (re.range "0" "9")) (re.+ (re.union (re.range "A" "Z") (re.++ (str.to.re "") (re.++ (re.+ (re.* (re.union (re.range "A" "Z") (re.++ (re.range "a" "z") (re.range "0" "9"))))) (re.union (re.++ (re.range "a" "z") (re.range "0" "9")) (re.* (str.to.re "G")))))))) (re.range "A" "Z"))))
(assert (str.in.re Domainname (re.union (re.range "0" "5") (re.++ (re.++ (re.++ (re.++ (str.to.re ".") (re.++ (re.++ (re.++ (re.union (re.union (re.union (re.union (re.++ (str.to.re ".") (re.range "0" "9")) (re.++ (re.union (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "") (str.to.re "5")))) (re.range "0" "9"))) (re.range "0" "4")) (re.++ (re.++ (re.union (str.to.re "_dH") (str.to.re ".")) (re.++ (re.++ (re.range "0" "4") (re.union (re.union (re.range "0" "9") (str.to.re "")) (re.union (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re ":") (str.to.re "/"))))))) (re.range "0" "5"))) (str.to.re "52"))) (str.to.re ".")) (re.range "0" "5")) (str.to.re "5")) (re.++ (re.range "0" "4") (re.union (re.++ (str.to.re "j") (re.range "0" "9")) (re.++ (re.++ (re.opt (re.union (str.to.re "P") (str.to.re "1"))) (re.opt (re.range "0" "9"))) (re.range "0" "9")))))) (re.range "0" "5")) (str.to.re "5")) (re.++ (re.range "0" "4") (re.++ (re.union (re.range "0" "9") (re.++ (re.opt (re.union (str.to.re "") (str.to.re "1"))) (re.opt (re.range "0" "9")))) (re.++ (str.to.re "2") (re.range "0" "9"))))))))
(check-sat)
