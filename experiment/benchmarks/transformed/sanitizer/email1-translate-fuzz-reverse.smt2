(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 60))
(assert (> (str.len Username) 0))
(assert (<= (str.to.int Domainname) 465))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ (str.++ Domainname "Z") Username)))
(assert (str.in.re Email (re.union (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (re.++ (re.+ (re.++ (re.union (re.range "A" "Z") (re.range "0" "9")) (re.range "a" "z"))) (re.+ (re.++ (str.to.re "") (re.+ (re.++ (re.++ (re.range "0" "9") (re.range "A" "Z")) (re.range "a" "z")))))) (str.to.re "Z")))))
(assert (str.in.re Domainname (re.++ (re.++ (re.++ (re.union (str.to.re "") (re.union (re.union (re.++ (re.range "0" "5") (str.to.re "5")) (re.++ (re.union (re.opt (re.++ (str.to.re "#") (str.to.re "C"))) (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9"))) (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "")))) (re.union (str.to.re "") (re.++ (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "2")) (re.union (re.opt (re.++ (str.to.re "1") (str.to.re ""))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9"))))) (re.union (str.to.re "2") (re.range "0" "5")))))) (re.union (re.++ (re.range "0" "5") (str.to.re "Vm")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "2")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (str.to.re ""))))))) (str.to.re "")) (re.++ (re.++ (re.union (re.opt (re.union (str.to.re "") (str.to.re ""))) (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9"))) (re.union (str.to.re "i") (re.union (re.range "0" "4") (re.range "0" "9")))) (re.union (str.to.re "kj2") (re.range "0" "5"))))))
(check-sat)
