(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 24))
(assert (> (str.to.int Username) 0))
(assert (<= (str.len Domainname) 88))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ (str.++ Domainname "@") Username)))
(assert (str.in.re Email (re.union (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (re.++ (re.* (re.++ (re.++ (re.range "0" "9") (re.range "A" "Z")) (re.range "a" "z"))) (re.+ (re.union (re.+ (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "")))) (str.to.re "@")))))
(assert (not (str.in.re Domainname (re.++ (re.union (str.to.re ".") (re.* re.allchar)) (re.* re.allchar)))))
(check-sat)
