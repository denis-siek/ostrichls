(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 17))
(assert (> (str.to.int Username) 0))
(assert (<= (str.len Domainname) 270))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ (str.++ Domainname "@") Username)))
(assert (str.in.re Email (re.union (re.union (re.union (re.+ (re.union (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))) (re.+ (re.++ (str.to.re ".") (re.* (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9"))))))) (str.to.re "")) (re.* (re.union (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))))))
(assert (str.in.re Domainname (re.++ (re.++ (re.++ (re.union (re.++ (re.union (re.++ (re.union (re.range "0" "5") (str.to.re "22")) (re.++ (re.++ (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "")) (re.++ (re.union (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "")))))) (str.to.re ".3=")) (re.union (re.++ (re.range "0" "5") (str.to.re "522")) (re.union (re.union (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "B=e")) (re.union (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "0{:") (str.to.re "nA"))))))) (str.to.re ".'\t'")) (re.++ (re.union (re.range "0" "5") (str.to.re "74%!2")) (re.++ (re.union (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "8u")) (re.++ (re.union (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "q<0") (str.to.re "dE"))))))) (str.to.re ".")) (re.union (re.union (re.range "0" "5") (str.to.re "28")) (re.union (re.++ (re.union (re.range "0" "9") (re.range "0" "4")) (str.to.re "6")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.++ (str.to.re "6O0") (str.to.re "D.")))))))))
(check-sat)
