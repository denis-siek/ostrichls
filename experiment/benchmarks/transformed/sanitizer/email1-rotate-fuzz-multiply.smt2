(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.to.int Username) 196))
(assert (> (str.to.int Username) 0))
(assert (<= (str.to.int Domainname) 848))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ "" (str.++ Domainname Username))))
(assert (str.in.re Email (re.++ (re.range "A" "Z") (re.union (re.++ (re.range "0" "9") (re.range "a" "z")) (re.+ (re.union (re.range "A" "Z") (re.++ (re.++ (re.union (re.++ (re.range "0" "9") (re.range "a" "z")) (re.* (str.to.re "GG"))) (re.+ (re.* (re.union (re.range "A" "Z") (re.++ (re.range "0" "9") (re.range "a" "z")))))) (str.to.re ""))))))))
(assert (str.in.re Domainname (re.union (re.range "0" "5") (re.++ (re.++ (re.++ (re.++ (re.range "0" "9") (str.to.re "22")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "") (str.to.re "11")))))) (re.range "0" "4")) (re.++ (str.to.re "55") (re.++ (re.range "0" "5") (re.++ (re.++ (re.++ (re.union (re.++ (re.range "0" "9") (str.to.re "jj")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "PP") (str.to.re "11")))))) (re.range "0" "4")) (re.++ (str.to.re "55") (re.++ (re.range "0" "5") (re.union (re.union (re.union (re.union (re.++ (re.range "0" "9") (str.to.re "..")) (re.++ (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "") (str.to.re "55")))))) (re.range "0" "4")) (re.++ (str.to.re "2255") (re.++ (re.++ (re.range "0" "5") (re.++ (re.union (re.union (re.range "0" "9") (str.to.re "")) (re.union (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "//") (str.to.re "::")))))) (re.range "0" "4"))) (re.union (str.to.re "HHdd__") (str.to.re ".."))))) (str.to.re ".."))))) (str.to.re ".."))))))))
(check-sat)
