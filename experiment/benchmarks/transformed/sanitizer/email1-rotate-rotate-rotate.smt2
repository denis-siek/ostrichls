(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 64))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 256))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ Username (str.++ "@" Domainname))))
(assert (str.in.re Email (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (re.union (re.+ (re.range "0" "9")) (re.++ (re.+ (re.union (str.to.re ".") (str.to.re "@"))) (re.++ (re.range "a" "z") (re.range "A" "Z")))) (re.union (re.+ (re.range "a" "z")) (re.union (re.range "0" "9") (re.range "A" "Z")))))))
(assert (str.in.re Domainname (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.union (re.++ (re.range "0" "9") (re.opt (re.range "0" "9"))) (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.++ (re.++ (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.range "0" "5"))) (re.union (str.to.re "25") (str.to.re "."))) (re.union (re.++ (re.++ (str.to.re "2") (str.to.re "25")) (re.union (re.range "0" "9") (re.++ (str.to.re "2") (str.to.re ".")))) (re.range "0" "5"))) (str.to.re "25")) (re.opt (re.range "0" "9"))))) (re.++ (str.to.re "2") (str.to.re ".")))) (re.union (re.range "0" "5") (re.++ (re.range "0" "9") (str.to.re "25"))))))))) (re.++ (str.to.re "2") (re.range "0" "5")))))))
(check-sat)
