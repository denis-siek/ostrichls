(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 64))
(assert (> 0 0))
(assert (<= (str.len Domainname) 256))
(assert (> (str.len Domainname) (str.len Username)))
(assert (= Email "A"))
(assert (str.in.re Email (re.++ (re.++ (re.++ (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.+ (re.++ (str.to.re ".") (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9"))))))) (re.* re.allchar)) (re.+ (re.union (re.range "a" "z") (re.union (re.range (str.++ (str.++ Domainname "@") Username) "Z") (re.range "0" "9")))))))
(assert (not (str.in.re Domainname (re.++ (re.++ (str.to.re "@") (str.to.re ".")) (re.* re.allchar)))))
(check-sat)
