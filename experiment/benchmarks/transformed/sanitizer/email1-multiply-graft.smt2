(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 128))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) (str.len Domainname)))
(assert (> 512 0))
(assert (= Email "0"))
(assert (str.in.re Email (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "@@") (re.++ (re.+ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re ".."))) (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))))))))
(assert (str.in.re Domainname (re.++ (re.union (re.++ (str.to.re "2255") (re.range "0" "5")) (re.union (re.++ (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (str.to.re "11"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "..") (re.++ (re.union (re.++ (str.to.re "2255") (re.range "0" "5")) (re.union (re.++ (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (str.to.re "11"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "..") (re.++ (re.union (re.++ (str.to.re "2255") (re.range "0" "5")) (re.union (re.++ (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (str.to.re "11"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "..") (re.union (re.++ (str.to.re "2255") (re.range "0" "5")) (re.union (re.++ (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (re.range (str.++ Username (str.++ "@@" Domainname)) "9"))) (re.++ (re.range "0" "9") (re.opt (str.to.re "11"))))))))))))))
(check-sat)
