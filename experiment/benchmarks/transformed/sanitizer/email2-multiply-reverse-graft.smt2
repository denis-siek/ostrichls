(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 128))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) (str.len Domainname)))
(assert (> 512 0))
(assert (= Email "0"))
(assert (str.in.re Email (re.++ (re.++ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.+ (re.++ (str.to.re "..") (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9"))))))) (re.* re.allchar)) (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range (str.++ (str.++ Domainname "@@") Username) "9")))))))
(assert (not (str.in.re Domainname (re.++ (re.++ (re.* re.allchar) (str.to.re "..")) (str.to.re "@@")))))
(check-sat)
