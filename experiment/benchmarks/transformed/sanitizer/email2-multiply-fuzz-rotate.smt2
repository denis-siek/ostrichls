(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 180))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 780))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ "" (str.++ Domainname Username))))
(assert (str.in.re Email (re.union (re.range "A" "Z") (re.++ (re.++ (re.range "0" "9") (re.range "a" "z")) (re.* (re.union (re.range "A" "Z") (re.++ (re.++ (re.++ (re.union (re.range "0" "9") (re.range "a" "z")) (re.* (str.to.re "G7"))) (re.* (re.+ (re.++ (re.range "A" "Z") (re.union (re.range "0" "9") (re.range "a" "z")))))) (str.to.re ""))))))))
(assert (not (str.in.re Domainname (re.union (re.+ (re.union re.allchar (re.* (str.to.re "k")))) re.allchar))))
(check-sat)
