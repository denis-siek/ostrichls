(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 64))
(assert (> 0 (str.len Username)))
(assert (<= (str.len Domainname) 256))
(assert (> 0 (str.len Domainname)))
(assert (= Email (str.++ Username "9")))
(assert (str.in.re Email (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "b") (re.++ (re.+ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "W"))) (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))))))))
(assert (str.in.re Domainname (re.++ (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "W") (re.++ (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "W") (re.++ (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "W") (re.union (re.++ (str.to.re "25") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.range "0" "@")) (re.++ (re.opt (re.union (re.++ (re.range "0" "4") (re.range "0" "9")) (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (str.to.re "0"))))))))))))))
(check-sat)
