(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 64))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 256))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ (str.++ "g" Username) Domainname)))
(assert (str.in.re Email (re.++ (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (re.+ (re.++ (re.union (re.range "A" "Z") (re.union (re.range "0" "9") (re.range "a" "z"))) (re.+ (str.to.re "p")))))) (re.++ (str.to.re "g") (re.++ (re.range "A" "Z") (re.+ (re.union (re.range "A" "Z") (re.union (re.range "0" "9") (re.range "a" "z")))))))))
(assert (str.in.re Domainname (re.++ (re.++ (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "9") (re.++ (re.++ (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "1")))) (re.opt (re.range "0" "9"))))) (re.++ (re.++ (re.union (re.range "0" "5") (str.to.re "p")) (re.++ (re.++ (re.union (re.++ (str.to.re "52") (re.union (re.range "0" "4") (re.++ (str.to.re "2") (re.++ (re.range "0" "9") (re.++ (re.++ (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "1")))) (re.opt (re.range "0" "9"))))))) (re.range "0" "5")) (re.++ (str.to.re "52") (str.to.re "p"))) (re.union (re.++ (str.to.re "52") (re.union (re.range "0" "4") (re.++ (str.to.re "2") (re.++ (re.range "0" "9") (re.++ (re.++ (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "1")))) (re.opt (re.range "0" "9"))))))) (re.range "0" "5")))) (str.to.re "p"))) (re.union (re.++ (str.to.re "52") (re.union (re.range "0" "4") (re.++ (str.to.re "2") (re.++ (re.range "0" "9") (re.++ (re.++ (re.range "0" "9") (re.opt (re.union (str.to.re "0") (str.to.re "1")))) (re.opt (re.range "0" "9"))))))) (re.range "0" "5"))) (re.range "0" "4"))))
(check-sat)
