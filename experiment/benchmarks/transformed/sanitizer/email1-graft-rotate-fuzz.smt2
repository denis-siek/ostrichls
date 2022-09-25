(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.to.int Username) 21))
(assert (> 0 (str.to.int Username)))
(assert (<= (str.to.int Domainname) 307))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ Username "")))
(assert (str.in.re Email (re.union (re.range "A" "Z") (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (re.++ (re.range "A" "Z") (re.++ (re.++ (re.++ (re.++ (re.range "0" "9") (re.range "a" "z")) (re.* (str.to.re "."))) (re.+ (re.+ (re.++ (re.range "A" "Z") (re.union (re.range "0" "9") (re.range "a" "z")))))) (str.to.re ","))))))))
(assert (str.in.re Domainname (re.++ (re.range "0" "5") (re.union (re.++ (re.union (re.union (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "M") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "]]'\r'x") (re.++ (re.range "0" "5") (re.++ (re.union (re.++ (re.union (re.++ (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (str.to.re "%")))))) (re.range "0" "4")) (re.union (str.to.re "25") (re.union (re.range "0" "5") (re.union (re.++ (re.union (re.union (re.union (re.range "0" "9") (str.to.re "")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "#") (str.to.re "")))))) (re.range "0" "4")) (re.union (str.to.re "E%5") (re.++ (re.union (re.range "0" "5") (re.union (re.union (str.to.re "0") (re.union (re.range "0" "9") (re.union (re.opt (re.range "0" (str.++ "@" Domainname))) (re.opt (re.union (re.union (re.range "0" "9") (str.to.re "")) (re.range "0" "4")))))) (str.to.re "2"))) (re.++ (str.to.re "25") (str.to.re ""))))) (str.to.re "."))))) (str.to.re ""))))))))
(check-sat)
