(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.to.int Username) 138))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 353))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ (str.++ Domainname "") Username)))
(assert (str.in.re Email (re.union (re.++ (re.++ (re.* (re.union (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))) (re.* (re.++ (str.to.re "E") (re.+ (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9"))))))) (str.to.re "")) (re.* (re.++ (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))))))
(assert (str.in.re Domainname (re.union (re.++ (re.union (re.++ (re.++ (re.++ (re.++ (re.++ (re.range "0" "5") (str.to.re "")) (re.union (re.++ (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.++ (str.to.re "*") (str.to.re "=")))))) (str.to.re "")) (re.union (re.++ (re.range "0" "5") (str.to.re "O'\x0c'xz")) (re.union (re.union (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "")) (re.++ (re.union (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.++ (str.to.re "") (str.to.re "B"))))))) (str.to.re ".")) (re.union (re.union (re.range "0" "5") (str.to.re "O")) (re.union (re.++ (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "z")) (re.++ (re.union (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "1"))))))) (str.to.re "v")) (re.++ (re.++ (re.range "0" "5") (str.to.re "")) (re.++ (re.++ (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "2")) (re.union (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.++ (str.to.re "?") (str.to.re "")))))))))
(check-sat)
