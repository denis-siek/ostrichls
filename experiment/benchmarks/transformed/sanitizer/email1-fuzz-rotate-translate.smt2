(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 48))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 48))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ "" (str.++ Domainname Username))))
(assert (str.in.re Email (re.union (re.range "A" "Z") (re.++ (re.union (re.range "0" "9") (re.range "a" "z")) (re.* (re.union (re.range "A" "Z") (re.union (re.++ (re.++ (re.++ (re.range "0" "9") (re.range "a" "z")) (re.+ (str.to.re ""))) (re.+ (re.* (re.union (re.range "A" "Z") (re.union (re.range "0" "9") (re.range "a" "z")))))) (str.to.re "q"))))))))
(assert (str.in.re Domainname (re.union (re.range "0" "5") (re.++ (re.union (re.++ (re.union (re.range "0" "9") (str.to.re "2")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (str.to.re "1")))))) (re.range "0" "4")) (re.union (str.to.re """""g""""%") (re.union (re.range "0" "5") (re.++ (re.++ (re.union (re.++ (re.++ (re.range "0" "9") (str.to.re "r")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (str.to.re "1")))))) (re.range "0" "4")) (re.union (str.to.re "") (re.++ (re.range "0" "5") (re.++ (re.++ (re.union (re.union (re.union (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "2") (re.union (re.++ (re.range "0" "5") (re.union (re.++ (re.union (re.range "0" "9") (str.to.re "I")) (re.++ (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "1")))))) (re.range "0" "4"))) (re.++ (str.to.re "") (str.to.re ""))))) (str.to.re ""))))) (str.to.re "`"))))))))
(check-sat)
