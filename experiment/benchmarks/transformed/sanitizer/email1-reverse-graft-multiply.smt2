(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) (str.len Domainname)))
(assert (> (str.len Username) 0))
(assert (<= 128 512))
(assert (> (str.len Domainname) 0))
(assert (= Email "99"))
(assert (str.in.re Email (re.++ (re.++ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.+ (re.++ (str.to.re "..") (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9"))))))) (str.to.re "@@")) (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))))))
(assert (str.in.re Domainname (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.union (re.++ (re.range "0" "5") (str.to.re "5522")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "22")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "11")))))) (str.to.re "..")) (re.union (re.++ (re.range "0" "5") (str.to.re "5522")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "22")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "11"))))))) (str.to.re "..")) (re.union (re.++ (re.range "0" "5") (str.to.re "5522")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "22")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" "9")) (re.opt (re.union (str.to.re "00") (str.to.re "11"))))))) (str.to.re "..")) (re.union (re.++ (re.range "0" "5") (str.to.re "5522")) (re.union (re.++ (re.++ (re.range "0" "9") (re.range "0" "4")) (str.to.re "22")) (re.++ (re.++ (re.opt (re.range "0" "9")) (re.range "0" (str.++ (str.++ Domainname "@@") Username))) (re.opt (str.to.re "11"))))))))
(check-sat)
