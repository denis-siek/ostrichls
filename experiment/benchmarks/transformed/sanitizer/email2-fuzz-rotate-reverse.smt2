(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 27))
(assert (> (str.to.int Username) 0))
(assert (<= (str.to.int Domainname) 468))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ (str.++ Username Domainname) "")))
(assert (str.in.re Email (re.union (re.range "A" "Z") (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (re.union (re.range "A" "Z") (re.union (re.++ (re.* (re.* (re.union (re.range "A" "Z") (re.++ (re.range "a" "z") (re.range "0" "9"))))) (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (str.to.re "8")))) (str.to.re "@"))))))))
(assert (not (str.in.re Domainname (re.union (re.+ (re.++ (re.* (str.to.re ".")) re.allchar)) re.allchar))))
(check-sat)
