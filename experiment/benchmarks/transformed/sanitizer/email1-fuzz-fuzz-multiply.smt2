(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.to.int Username) 74))
(assert (> (str.to.int Username) 0))
(assert (<= (str.len Domainname) 116))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ Username (str.++ "" Domainname))))
(assert (str.in.re Email (re.++ (re.+ (re.union (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "") (re.++ (re.+ (re.++ (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re ""))) (re.+ (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))))))))
(assert (str.in.re Domainname (re.union (re.union (re.++ (str.to.re "''//") (re.range "0" "5")) (re.++ (re.union (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "<<") (str.to.re "xx"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "'''\x0c''\x0c'''") (re.++ (re.union (re.++ (str.to.re "") (re.range "0" "5")) (re.union (re.++ (str.to.re "") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (str.to.re ""))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "") (re.++ (re.++ (re.++ (str.to.re "") (re.range "0" "5")) (re.++ (re.++ (str.to.re "") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "") (re.++ (re.++ (str.to.re "") (re.range "0" "5")) (re.++ (re.++ (str.to.re "kk") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "@@") (str.to.re ""))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9"))))))))))))))
(check-sat)
