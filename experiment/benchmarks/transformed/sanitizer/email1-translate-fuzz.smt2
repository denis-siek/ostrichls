(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 90))
(assert (> (str.to.int Username) 0))
(assert (<= (str.len Domainname) 474))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ Username (str.++ "?" Domainname))))
(assert (str.in.re Email (re.union (re.+ (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "?") (re.++ (re.+ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "{"))) (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))))))))
(assert (str.in.re Domainname (re.++ (re.++ (re.union (str.to.re "2") (re.range "0" "5")) (re.union (re.union (str.to.re "") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "X") (str.to.re "l"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "") (re.++ (re.union (re.union (str.to.re "2") (re.range "0" "5")) (re.++ (re.union (str.to.re "Q") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "") (re.union (re.++ (re.union (str.to.re "g5") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.union (str.to.re "0") (str.to.re "1"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "") (re.++ (re.++ (str.to.re "") (re.range "0" "5")) (re.++ (re.++ (str.to.re "|") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "0") (str.to.re ""))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9"))))))))))))))
(check-sat)
