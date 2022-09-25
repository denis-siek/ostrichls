(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 11))
(assert (> (str.len Username) 0))
(assert (<= (str.to.int Domainname) 535))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ "F@" (str.++ Domainname Username))))
(assert (str.in.re Email (re.++ (re.range "A" "Z") (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.* (re.union (re.range "A" "Z") (re.union (re.++ (re.++ (re.union (re.range "0" "9") (re.range "a" "z")) (re.* (str.to.re ""))) (re.* (re.* (re.union (re.range "A" "Z") (re.union (re.range "0" "9") (re.range "a" "z")))))) (str.to.re ""))))))))
(assert (str.in.re Domainname (re.++ (re.range "0" "5") (re.++ (re.union (re.++ (re.union (re.range "0" "9") (str.to.re ",u^")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "Cwo") (str.to.re "vB")))))) (re.range "0" "4")) (re.++ (str.to.re "5") (re.++ (re.range "0" "5") (re.++ (re.++ (re.++ (re.union (re.++ (re.range "0" "9") (str.to.re "20")) (re.++ (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "a1")))))) (re.range "0" "4")) (re.++ (str.to.re "255") (re.++ (re.range "0" "5") (re.union (re.++ (re.++ (re.++ (re.union (re.range "0" "9") (str.to.re "2")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "") (str.to.re "PB")))))) (re.range "0" "4")) (re.++ (str.to.re "y^~") (re.union (re.++ (re.range "0" "5") (re.union (re.union (re.union (re.range "0" "9") (str.to.re "x62")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "D-") (str.to.re "")))))) (re.range "0" "4"))) (re.++ (str.to.re "2") (str.to.re ""))))) (str.to.re "**."))))) (str.to.re ".."))))))))
(check-sat)
