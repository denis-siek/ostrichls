(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) (str.len Domainname)))
(assert (> (str.len Username) 0))
(assert (<= 64 256))
(assert (> (str.len Domainname) 0))
(assert (= Email "9"))
(assert (str.in.re Email (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "@") (re.++ (re.+ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "."))) (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))))))))
(assert (str.in.re Domainname (re.++ (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (str.to.re "1")) (re.++ (re.range "0" (str.++ Username (str.++ "@" Domainname))) (re.opt (re.range "0" "9")))))) (re.++ (str.to.re ".") (re.++ (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re ".") (re.++ (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re ".") (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9"))))))))))))))
(check-sat)
